use automerge_repo::fs_store::FsStore;
use automerge_repo::{ConnDirection, DocHandle, DocumentId, Repo, Storage, StorageError};
use autosurgeon::{hydrate, reconcile, Hydrate, Reconcile};
use axum::extract::State;
use axum::routing::{get, put};
use axum::{Json, Router};
use clap::Parser;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
use std::fmt::{Display, Formatter};
use std::str::FromStr;
use std::sync::{Arc, Mutex};
use tempfile::TempDir;
use tokio::net::{TcpListener, TcpStream};
use tokio::runtime::Handle;
use tokio::sync::mpsc::{self, Receiver, Sender};
use tokio::sync::oneshot;
use tokio::sync::watch;
use tokio::time::{sleep, Duration};

fn is_leader(replica: &Replica, id: &ReplicaId) -> bool {
    replica.view.0.checked_rem(3).unwrap() == u64::from_str(&id.0).unwrap()
}

async fn get_doc_id(State(state): State<Arc<AppState>>) -> Json<DocumentId> {
    Json(state.doc_handle.document_id())
}

async fn read(State(state): State<Arc<AppState>>) -> Json<Option<Reply>> {
    let (tx, rx) = oneshot::channel();
    let _ = state.command_sender.send((ClientOp::Read, tx)).await;
    Json(rx.await.unwrap_or(None))
}

async fn incr(State(state): State<Arc<AppState>>) -> Json<Option<Reply>> {
    let (tx, rx) = oneshot::channel();
    let _ = state.command_sender.send((ClientOp::Incr, tx)).await;
    Json(rx.await.unwrap_or(None))
}

fn execute_state_machine(
    pending_client_command: &mut Option<oneshot::Sender<Option<Reply>>>,
    log: &[LogEntry],
    commit: usize,
) {
    let mut state = 0;
    for (index, entry) in log.iter().enumerate() {
        if index == commit {
            break;
        }
        
        match &entry.op {
            ClientOp::Read => {},
            ClientOp::Incr => state += 1,
        }
        
        if index == commit - 1 {
            pending_client_command.take().unwrap().send(Some(Reply(state))).unwrap();
        }
    }
}

async fn run_primary_algorithm(
    doc_handle: &DocHandle,
    replica_id: &ReplicaId,
    mut command_receiver: Receiver<(ClientOp, oneshot::Sender<Option<Reply>>)>,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    let mut incoming_client_commands: VecDeque<(ClientOp, oneshot::Sender<Option<Reply>>)> =
        Default::default();
    let mut pending_client_command: Option<oneshot::Sender<Option<Reply>>> =
        Default::default();
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            {
                let our_info = vsr.replicas.get_mut(replica_id).unwrap();

                if !is_leader(our_info, replica_id) || !our_info.status.is_normal() {
                    // Reset the client command state,
                    // send back None to all pending commands.
                    incoming_client_commands.drain(..).for_each(|(_, chan)| {
                        chan.send(None).unwrap();
                    });
                    if let Some(chan) = pending_client_command.take() {
                        chan.send(None).unwrap();
                    }

                    // Remove uncommitted entries.
                    our_info
                        .log
                        .split_off(our_info.commit_num.0.try_into().unwrap());
                    return;
                }
            }

            // HandleRequest.
            if !incoming_client_commands.is_empty() {
                let our_info = vsr.replicas.get_mut(replica_id).unwrap();
                if our_info.op_num.0 == our_info.commit_num.0 {
                    let (command, sender) = incoming_client_commands.pop_front().unwrap();
                    pending_client_command = Some(sender);
                    our_info.op_num.0 += 1;
                    our_info.log.push(LogEntry {
                        client: ClientId(String::new()),
                        op: command,
                    });
                }
            }

            // HandlePrepareOk.
            let (our_view, our_commit) = vsr
                .replicas
                .iter()
                .find_map(|(id, info)| {
                    if id == replica_id {
                        Some((info.view, info.commit_num))
                    } else {
                        None
                    }
                })
                .unwrap();
            let has_quorum = vsr
                .replicas
                .iter()
                .find(|(id, info)| {
                    id != &replica_id && info.view == our_view && info.op_num.0 == our_commit.0 + 1
                })
                .is_some();
            if has_quorum {
                let our_info = vsr.replicas.get_mut(replica_id).unwrap();
                our_info.commit_num.0 += 1;
                println!("Committed {:?}", our_info.commit_num);
                execute_state_machine(
                    &mut pending_client_command,
                    &our_info.log,
                    our_info.commit_num.0.try_into().unwrap(),
                );
            }

            let mut tx = doc.transaction();
            reconcile(&mut tx, &vsr).unwrap();
            tx.commit();
        });
        tokio::select! {
            cmd = command_receiver.recv() => {
                if let Some(cmd) = cmd {
                    incoming_client_commands.push_back(cmd);
                }
            }
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_backup_algorithm(
    doc_handle: DocHandle,
    replica_id: &ReplicaId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            let (our_op_num, our_commit_num, our_view) = {
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();

                if is_leader(our_info, replica_id) || !our_info.status.is_normal() {
                    return;
                }
                (our_info.op_num, our_info.commit_num, our_info.view)
            };

            let leader_info_updated = vsr.replicas.iter().find_map(|(id, info)| {
                if info.view == our_view
                    && (info.op_num > our_op_num || info.commit_num > our_commit_num)
                    && is_leader(info, id)
                {
                    Some(info.clone())
                } else {
                    None
                }
            });

            // HandlePrepare.
            if let Some(info) = leader_info_updated {
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                our_info.commit_num = info.commit_num;
                our_info.op_num = info.op_num;
                our_info.log = info.log;
                println!("Prepared {:?}", our_info.op_num);
                let mut tx = doc.transaction();
                reconcile(&mut tx, &vsr).unwrap();
                tx.commit();
            }
        });
        tokio::select! {
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_state_transfer_algorithm(
    doc_handle: DocHandle,
    replica_id: &ReplicaId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();
            let max_view = {
                vsr.replicas
                    .iter()
                    .map(|(_, info)| info.view)
                    .max()
                    .unwrap()
            };
            let max_op = {
                vsr.replicas
                    .iter()
                    .map(|(_, info)| info.op_num)
                    .max()
                    .unwrap()
            };

            // StartStateTransfer.
            let should_transfer = {
                let our_info = vsr.replicas.get(&replica_id).unwrap();
                our_info.view < max_view || our_info.op_num < max_op
            };

            // HandleGetState.
            let from_info = if should_transfer {
                println!("Start state transfer");
                vsr.replicas.iter().find_map(|(_, info)| {
                    if info.view == max_view && info.op_num == max_op {
                        Some(info.clone())
                    } else {
                        None
                    }
                })
            } else {
                None
            };

            // HandleNewState.
            if let Some(from) = from_info {
                println!("Finishing state transfer");
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                our_info.view = from.view;
                our_info.op_num = from.op_num;
                our_info.commit_num = from.commit_num;
                our_info.log = from.log;
                let mut tx = doc.transaction();
                reconcile(&mut tx, &vsr).unwrap();
                tx.commit();
            }
        });
        tokio::select! {
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_view_change_algorithm(
    doc_handle: DocHandle,
    replica_id: ReplicaId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    let mut start_view_change = false;
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            // ReplacePrimary(every 3 secs).
            {
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                if start_view_change {
                    println!("Start view change: {:?}", our_info.view);
                    if our_info.status.is_normal() {
                        our_info.last_normal = our_info.view;
                        our_info.status.start_view_change();
                    }
                    our_info.view.0 += 1;     
                    start_view_change = false;
                    let mut tx = doc.transaction();
                    reconcile(&mut tx, &vsr).unwrap();
                    tx.commit();
                    return;
                }
            }

            // NoticeViewChange
            {
                let max_view = {
                    vsr.replicas
                        .iter()
                        .map(|(_, info)| info.view)
                        .max()
                        .unwrap()
                };
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                if max_view > our_info.view && our_info.status.is_normal() {
                    println!("Notice view change: {:?}", our_info.view);
                    our_info.last_normal = our_info.view;
                    our_info.view = max_view;
                    our_info.status.start_view_change();
                    let mut tx = doc.transaction();
                    reconcile(&mut tx, &vsr).unwrap();
                    tx.commit();
                    return;
                }
            }

            // CompleteViewChange
            {
                let same_view = {
                    let our_info = vsr.replicas.get(&replica_id).unwrap();
                    vsr.replicas
                        .iter()
                        .filter(|(_, info)| info.view == our_info.view)
                        .count()
                };
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                if same_view > 1
                    && our_info.status.is_view_change()
                    && is_leader(our_info, &replica_id)
                {
                    println!("Complete view change: {:?}", our_info.view);
                    our_info.last_normal = our_info.view;
                    our_info.status.complete_view_change();
                    let mut tx = doc.transaction();
                    reconcile(&mut tx, &vsr).unwrap();
                    tx.commit();
                    return;
                }
            }

            // HandleStartView
            {
                let leader_is_normal = {
                    let our_info = vsr.replicas.get(&replica_id).unwrap();
                    vsr.replicas
                        .iter()
                        .filter(|(id, info)| {
                            info.view == our_info.view
                                && is_leader(info, id)
                                && info.status.is_normal()
                        })
                        .count()
                };
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                if leader_is_normal > 0 && our_info.status.is_view_change() {
                    println!("Start new view: {:?}", our_info.view);
                    our_info.last_normal = our_info.view;
                    our_info.status.complete_view_change();
                    let mut tx = doc.transaction();
                    reconcile(&mut tx, &vsr).unwrap();
                    tx.commit();
                    return;
                }
            }
        });
        tokio::select! {
            _ = sleep(Duration::from_millis(3000)) => {
                start_view_change = true;
                println!("Should see need for view change");
            },
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_recovery_algorithm(
    doc_handle: DocHandle,
    replica_id: &ReplicaId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            {
                let our_info = vsr.replicas.get(&replica_id).unwrap();
                if !our_info.status.is_recovering() {
                    return;
                }
            }

            let max_view = vsr
                .replicas
                .iter()
                .filter_map(|(id, info)| {
                    Some(info.view)
                })
                .max()
                .unwrap();
            if let Some(leader_info) = vsr.replicas.iter().find_map(|(id, info)| {
                if info.status.is_normal() && info.view == max_view && is_leader(info, id) {
                    Some(info.clone())
                } else {
                    None
                }
            }) {
                // Recover.
                let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
                our_info.view = leader_info.view;
                our_info.op_num = leader_info.op_num;
                our_info.commit_num = leader_info.commit_num;
                our_info.log = leader_info.log;
                our_info.last_normal = our_info.view;
                our_info.status.complete_recovery();
                let mut tx = doc.transaction();
                reconcile(&mut tx, &vsr).unwrap();
                tx.commit();
                println!("Recovered");
            }
        });
        tokio::select! {
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn request_increment(
    http_addrs: Vec<String>,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    let client = reqwest::Client::new();
    let mut last = 0;
    loop {
        for addr in http_addrs.iter() {
            tokio::select! {
                _ = sleep(Duration::from_millis(1000)) => {},
                _ = shutdown.changed() => return,
            };
            let url = format!("http://{}/incr", addr);
            let res = client.put(url).send().await;
            if let Ok(new) = res {
                let json_res = new.json().await;
                if let Ok(Some(new)) = json_res {
                    println!("Got new increment: {:?}, versus old one: {:?}", new, last);
                    assert!(new > last);
                    last = new;
                }
            }
        }
    }
}

async fn request_read(http_addrs: Vec<String>, mut shutdown: tokio::sync::watch::Receiver<()>) {
    let client = reqwest::Client::new();
    let mut last = 0;
    loop {
        for addr in http_addrs.iter() {
            tokio::select! {
                _ = sleep(Duration::from_millis(1000)) => {},
                _ = shutdown.changed() => return,
            };
            let url = format!("http://{}/read", addr);
            let res = client.get(url).send().await;
            if let Ok(new) = res {
                let json_res = new.json().await;
                if let Ok(Some(new)) = json_res {
                    println!("Got new read: {:?}, versus old one: {:?}", new, last);
                    assert!(new >= last);
                    last = new;
                }
            }
        }
    }
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    bootstrap: bool,
    #[arg(long)]
    recover: bool,
    #[arg(long)]
    replica_id: String,
}

struct AppState {
    doc_handle: DocHandle,
    command_sender: Sender<(ClientOp, oneshot::Sender<Option<Reply>>)>,
    replica_id: ReplicaId,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, Deserialize, Serialize)]
struct Reply(u64);

#[derive(Debug, Clone, Reconcile, Hydrate)]
enum ClientOp {
    Read,
    Incr,
}

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Nounce {
    replica: ReplicaId,
    value: u64,
}

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct LogEntry {
    client: ClientId,
    op: ClientOp,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, PartialOrd, Ord)]
struct ReplicaId(String);

impl Display for ReplicaId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for ReplicaId {
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl From<String> for ReplicaId {
    fn from(s: String) -> Self {
        Self(s)
    }
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, PartialOrd, Ord)]
struct ClientId(String);

impl Display for ClientId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for ClientId {
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl From<String> for ClientId {
    fn from(s: String) -> Self {
        Self(s)
    }
}

#[derive(Debug, Clone, Reconcile, Hydrate, Default, Eq, PartialEq)]
enum ReplicaStatus {
    #[default]
    Normal,
    Recovering,
    ViewChange,
}

impl ReplicaStatus {
    fn is_normal(&self) -> bool {
        matches!(self, ReplicaStatus::Normal)
    }

    fn is_recovering(&self) -> bool {
        matches!(self, ReplicaStatus::Recovering)
    }

    fn complete_recovery(&mut self) {
        assert_eq!(*self, ReplicaStatus::Recovering);
        *self = ReplicaStatus::Normal;
    }

    fn is_view_change(&self) -> bool {
        matches!(self, ReplicaStatus::ViewChange)
    }

    fn start_view_change(&mut self) {
        assert_eq!(*self, ReplicaStatus::Normal);
        *self = ReplicaStatus::ViewChange;
    }

    fn complete_view_change(&mut self) {
        assert_eq!(*self, ReplicaStatus::ViewChange);
        *self = ReplicaStatus::Normal;
    }
}

#[derive(Debug, Clone, Copy, Reconcile, Hydrate, Default, Eq, PartialEq, Ord, PartialOrd)]
struct ViewNum(u64);

#[derive(Debug, Clone, Copy, Reconcile, Hydrate, Default, Eq, PartialEq, Ord, PartialOrd)]
struct OpNum(u64);

#[derive(Debug, Clone, Copy, Reconcile, Hydrate, Default, Eq, PartialEq, Ord, PartialOrd)]
struct CommitNum(u64);

#[derive(Debug, Clone, Reconcile, Hydrate, Default)]
struct Replica {
    view: ViewNum,
    last_normal: ViewNum,
    op_num: OpNum,
    commit_num: CommitNum,
    log: Vec<LogEntry>,
    status: ReplicaStatus,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate)]
struct VSR {
    replicas: HashMap<ReplicaId, Replica>,
}

struct NoStorage;

impl Storage for NoStorage {
    fn get(&self, _id: DocumentId) -> BoxFuture<'static, Result<Option<Vec<u8>>, StorageError>> {
        Box::pin(futures::future::ready(Ok(None)))
    }

    fn list_all(&self) -> BoxFuture<'static, Result<Vec<DocumentId>, StorageError>> {
        Box::pin(futures::future::ready(Ok(vec![])))
    }

    fn append(
        &self,
        _id: DocumentId,
        _changes: Vec<u8>,
    ) -> BoxFuture<'static, Result<(), StorageError>> {
        Box::pin(futures::future::ready(Ok(())))
    }

    fn compact(
        &self,
        _id: DocumentId,
        _full_doc: Vec<u8>,
    ) -> BoxFuture<'static, Result<(), StorageError>> {
        Box::pin(futures::future::ready(Ok(())))
    }
}

#[tokio::main]
async fn main() {
    let args = Args::parse();
    let bootstrap = args.bootstrap;
    let recover = args.recover;
    let replica_id = args.replica_id.clone();
    let handle = Handle::current();

    if bootstrap {
        assert!(!recover);
    }

    // All customers, including ourself.
    let customers: Vec<String> = vec!["0", "1", "2"]
        .into_iter()
        .map(|id| id.to_string())
        .collect();

    // Addrs of peers.
    let http_addrs: Vec<String> = customers
        .iter()
        .filter(|id| id != &&args.replica_id)
        .map(|id| format!("0.0.0.0:300{}", id))
        .collect();
    let tcp_addrs: Vec<String> = customers
        .iter()
        .filter(|id| id != &&args.replica_id)
        .map(|id| format!("127.0.0.1:234{}", id))
        .collect();

    // Our addrs
    let our_http_addr = format!("0.0.0.0:300{}", replica_id);
    let our_tcp_addr = format!("127.0.0.1:234{}", replica_id);

    // Create a repo.
    let repo = Repo::new(None, Box::new(NoStorage));
    let repo_handle = repo.run();

    // Start a tcp server.
    let repo_clone = repo_handle.clone();
    handle.spawn(async move {
        let listener = TcpListener::bind(our_tcp_addr).await.unwrap();
        loop {
            match listener.accept().await {
                Ok((socket, addr)) => {
                    repo_clone
                        .connect_tokio_io(addr, socket, ConnDirection::Incoming)
                        .await
                        .unwrap();
                }
                Err(e) => println!("couldn't get client: {:?}", e),
            }
        }
    });

    // Connect to the other peers.
    let repo_clone = repo_handle.clone();
    handle.spawn(async move {
        for addr in tcp_addrs {
            let stream = loop {
                let res = TcpStream::connect(addr.clone()).await;
                if res.is_err() {
                    sleep(Duration::from_millis(100)).await;
                    continue;
                }
                break res.unwrap();
            };
            repo_clone
                .connect_tokio_io(addr, stream, ConnDirection::Outgoing)
                .await
                .unwrap();
        }
    });

    let doc_handle = if bootstrap {
        let mut vsr: VSR = Default::default();
        for replica_id in customers.clone() {
            let participant = Default::default();
            vsr.replicas
                .insert(ReplicaId(replica_id.to_string()), participant);
        }

        // The initial document.
        let doc_handle = repo_handle.new_document();
        doc_handle.with_doc_mut(|doc| {
            let mut tx = doc.transaction();
            reconcile(&mut tx, &vsr).unwrap();
            tx.commit();
        });

        doc_handle
    } else {
        // Get the id of the shared document.
        let client = reqwest::Client::new();
        let mut doc_id = None;
        for addr in http_addrs.iter() {
            let url = format!("http://{}/get_doc_id", addr);
            let res = client.get(url).send().await;
            if res.is_err() {
                continue;
            }
            let data = res.unwrap().json().await;
            if data.is_err() {
                continue;
            }
            doc_id = Some(data.unwrap());
            break;
        }
        assert!(doc_id.is_some());
        // Get the document.
        repo_handle.request_document(doc_id.unwrap()).await.unwrap()
    };

    let replica_id = ReplicaId(replica_id);

    if recover {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            let our_info = vsr.replicas.get_mut(&replica_id).unwrap();
            our_info.status = ReplicaStatus::Recovering;
            let mut tx = doc.transaction();
            reconcile(&mut tx, &vsr).unwrap();
            tx.commit();
        });
    }

    let (leader_tx, leader_rx) = mpsc::channel(100);
    let app_state = Arc::new(AppState {
        doc_handle: doc_handle.clone(),
        command_sender: leader_tx,
        replica_id: replica_id.clone(),
    });

    let (shutdown_tx, shutdown_rx) = watch::channel(());

    let doc_handle_clone = doc_handle.clone();
    let id = replica_id.clone();
    let shutdown = shutdown_rx.clone();
    let primary = handle.spawn(async move {
        run_primary_algorithm(&doc_handle_clone, &id, leader_rx, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = replica_id.clone();
    let shutdown = shutdown_rx.clone();
    let backup = handle.spawn(async move {
        run_backup_algorithm(doc_handle_clone, &id, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = replica_id.clone();
    let shutdown = shutdown_rx.clone();
    let view_change = handle.spawn(async move {
        run_view_change_algorithm(doc_handle_clone, id, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = replica_id.clone();
    let shutdown = shutdown_rx.clone();
    let state_transfer = handle.spawn(async move {
        run_state_transfer_algorithm(doc_handle_clone, &id, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = replica_id.clone();
    let shutdown = shutdown_rx.clone();
    let primary = handle.spawn(async move {
        run_recovery_algorithm(doc_handle_clone, &id, shutdown).await;
    });

    let http_addrs_clone = http_addrs.clone();
    let shutdown = shutdown_rx.clone();
    let incrementer = handle.spawn(async move {
        // Continuously request new increments.
        request_increment(http_addrs_clone, shutdown).await;
    });

    let shutdown = shutdown_rx.clone();
    let reader = handle.spawn(async move {
        // Continuously request new reads.
        request_read(http_addrs, shutdown).await;
    });

    let app = Router::new()
        .route("/get_doc_id", get(get_doc_id))
        .route("/read", get(read))
        .route("/incr", put(incr))
        .with_state(app_state.clone());
    let serve = axum::Server::bind(&our_http_addr.parse().unwrap()).serve(app.into_make_service());
    tokio::select! {
        _ = serve.fuse() => {},
        _ = tokio::signal::ctrl_c().fuse() => {

            // Send shutdown signal.
            shutdown_tx.send(()).unwrap();

            // Join on tasks.
            incrementer.await.unwrap();
            reader.await.unwrap();
            primary.await.unwrap();
            backup.await.unwrap();
            view_change.await.unwrap();
            state_transfer.await.unwrap();

            // Stop repo.
            Handle::current()
                .spawn_blocking(|| {
                    repo_handle.stop().unwrap();
                })
                .await
                .unwrap();
        }
    }
}

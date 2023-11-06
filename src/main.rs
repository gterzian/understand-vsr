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
use std::sync::{Arc, Mutex};
use tempfile::TempDir;
use tokio::net::{TcpListener, TcpStream};
use tokio::runtime::Handle;
use tokio::sync::mpsc::{self, Receiver, Sender};
use tokio::sync::oneshot;
use tokio::sync::watch;
use tokio::time::{sleep, Duration};

const MAX: usize = 1000;

async fn get_doc_id(State(state): State<Arc<AppState>>) -> Json<DocumentId> {
    Json(state.doc_handle.document_id())
}

async fn read(State(state): State<Arc<AppState>>) -> Json<Option<Reply>> {
    let replica_id = state.replica_id.clone();
    let is_leader = state.doc_handle.with_doc_mut(|doc| {
        let mut vsr: VSR = hydrate(doc).unwrap();

        // Run election
        let _ = leader_algorithm(&mut vsr, &replica_id);

        let our_info = vsr.participants.get(&replica_id).unwrap();
        our_info.is_leader
    });

    if !is_leader {
        return Json(None);
    }

    let (tx, rx) = oneshot::channel();
    let _ = state.command_sender.send((ClientOp::Read, tx)).await;
    Json(rx.await.unwrap_or(None))
}

async fn incr(State(state): State<Arc<AppState>>) -> Json<Option<Reply>> {
    let replica_id = state.replica_id.clone();
    let is_leader = state.doc_handle.with_doc_mut(|doc| {
        let mut vsr: VSR = hydrate(doc).unwrap();

        // Run election
        let _ = leader_algorithm(&mut vsr, &replica_id);

        let our_info = vsr.participants.get(&replica_id).unwrap();
        our_info.is_leader
    });

    if !is_leader {
        return Json(None);
    }

    let (tx, rx) = oneshot::channel();
    let _ = state.command_sender.send((ClientOp::Incr, tx)).await;
    Json(rx.await.unwrap_or(None))
}

fn leader_algorithm(election: &mut VSR, replica_id: &ReplicaId) -> ElectionOutcome {
    let (our_epoch, our_past_leadership) = {
        let our_info = election.participants.get_mut(replica_id).unwrap();
        (our_info.epoch, our_info.is_leader)
    };

    let mut our_new_leadership = true;
    for (id, info) in election.participants.iter() {
        if id == replica_id {
            continue;
        }
        let our_epoch_minus_theirs = our_epoch.saturating_sub(info.epoch);
        if replica_id > id {
            if our_epoch_minus_theirs < 3 && info.is_leader {
                our_new_leadership = false;
            }
        } else if our_epoch_minus_theirs < 3 && !our_past_leadership {
            our_new_leadership = false;
        }
    }

    let outcome = if !our_past_leadership && our_new_leadership {
        ElectionOutcome::NewlyElected
    } else if our_past_leadership && !our_new_leadership {
        ElectionOutcome::SteppedDown
    } else {
        ElectionOutcome::Unchanged
    };

    let max_epoch = election
        .participants
        .values()
        .map(|info| info.epoch)
        .max()
        .unwrap();
    let our_info = election.participants.get_mut(replica_id).unwrap();
    our_info.epoch = if let ElectionOutcome::NewlyElected = outcome {
        max_epoch + 1
    } else {
        max_epoch
    };
    our_info.is_leader = our_new_leadership;
    outcome
}

fn execute_state_machine(
    ballot_number_to_client_request: &mut [Option<oneshot::Sender<Option<Reply>>>],
    log: &[Option<LogEntry>],
) {
    let mut state = 0;
    for (index, entry) in log.iter().enumerate() {
        let cmd = match entry {
            Some(entry) => &entry.op,
            None => break,
        };
        let new_execution = match cmd {
            ClientOp::Read => ballot_number_to_client_request[index].take(),
            ClientOp::Incr => {
                state += 1;
                ballot_number_to_client_request[index].take()
            }
        };
        if let Some(chan) = new_execution {
            chan.send(Some(Reply(state))).unwrap();
        }
    }
}

async fn run_primary_algorithm(
    doc_handle: &DocHandle,
    replica_id: &ReplicaId,
    mut command_receiver: Receiver<(ClientOp, oneshot::Sender<Option<Reply>>)>,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    let mut pending_client_commands: VecDeque<(ClientOp, oneshot::Sender<Option<Reply>>)> =
        Default::default();
    let mut ballot_number_to_client_request: Vec<Option<oneshot::Sender<Option<Reply>>>> = vec![];
    for _ in 0..MAX {
        ballot_number_to_client_request.push(None);
    }
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            let mut tx = doc.transaction();
            reconcile(&mut tx, &vsr).unwrap();
            tx.commit();
        });
        tokio::select! {
            cmd = command_receiver.recv() => {
                if let Some(cmd) = cmd {
                    pending_client_commands.push_back(cmd);
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

            let mut tx = doc.transaction();
            reconcile(&mut tx, &vsr).unwrap();
            tx.commit();
        });
        tokio::select! {
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_heartbeat_algorithm(
    doc_handle: DocHandle,
    replica_id: ReplicaId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut vsr: VSR = hydrate(doc).unwrap();

            let our_info = vsr.participants.get_mut(&replica_id).unwrap();
            our_info.epoch = our_info.epoch.checked_add(1).unwrap_or(0);

            let mut tx = doc.transaction();
            reconcile(&mut tx, &vsr).unwrap();
            tx.commit();
        });
        tokio::select! {
            _ = sleep(Duration::from_millis(3000)) => {},
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
    replica_id: String,
}

struct AppState {
    doc_handle: DocHandle,
    command_sender: Sender<(ClientOp, oneshot::Sender<Option<Reply>>)>,
    replica_id: ReplicaId,
}

#[derive(Debug, PartialEq)]
enum ElectionOutcome {
    NewlyElected,
    SteppedDown,
    Unchanged,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, Deserialize, Serialize)]
struct Reply(u64);

#[derive(Debug, Clone, Reconcile, Hydrate)]
enum ClientOp {
    Read,
    Incr,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct View(u64);

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

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Replica {
    /// Election data.
    epoch: u64,
    is_leader: bool,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate)]
struct VSR {
    participants: HashMap<ReplicaId, Replica>,
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
    let replica_id = args.replica_id.clone();
    let handle = Handle::current();

    // All customers, including ourself.
    let customers: Vec<String> = vec!["1", "2", "3"]
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
            let participant = Replica {
                epoch: 0,
                is_leader: false,
            };
            vsr.participants
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

    let (tx, rx) = mpsc::channel(100);

    let app_state = Arc::new(AppState {
        doc_handle: doc_handle.clone(),
        command_sender: tx,
        replica_id: replica_id.clone(),
    });

    let (shutdown_tx, shutdown_rx) = watch::channel(());

    let doc_handle_clone = doc_handle.clone();
    let id = replica_id.clone();
    let shutdown = shutdown_rx.clone();
    let primary = handle.spawn(async move {
        run_primary_algorithm(&doc_handle_clone, &id, rx, shutdown).await;
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
    let heartbeat = handle.spawn(async move {
        run_heartbeat_algorithm(doc_handle_clone, id, shutdown).await;
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
            heartbeat.await.unwrap();

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

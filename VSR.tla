-------------------------------- MODULE VSR --------------------------------
EXTENDS FiniteSets, Naturals
VARIABLE viewNum, status, opNum, log, commitNum, 
            msgs, clientTable, clientRequest, lastNormal, nounce
CONSTANT N, Empty, F
----------------------------------------------------------------------------
\* Specification based on "Viewstamped Replication Revisited"
\* found at https://dspace.mit.edu/handle/1721.1/71763
\*
\* Covers only:
\* 1. Normal operation(without some client interaction parts).
\* 2. View change.
\* 3. Recovery.

Replica == 0..N
Client == 0..N
View == 0..N
Op == 0..N
LogEntry == Client \X Op

ASSUME Empty \notin LogEntry

\* Use replica groups of size 2f + 1.
ASSUME (2*F) + 1 = N+1 

\* Round-robin primary using viewNum
IsPrimary(r) == viewNum[r] % N = r

\* The set of messages.
\*
\* We use a set to model:
\* 1. Re-ordering and re-delivery of messages.
\* 2. The local per-replica buffer 
\*    of messages not ready for processing(same as re-delivery when ready).
Message == 
           \* Client request.
           [type: {"REQUEST"}, 
            clientId: Client, 
            requestNum: Op]
            \cup
            \* Normal operation 
            [type: {"PREPARE"},
             v: View,
             m: [type: {"REQUEST"}, 
                 clientId: Client, 
                 requestNum: Op],
             n: Op,
             k: Op
             ]
             \cup
             [type: {"PREPAREOK"}, 
              v: View,
              n: Op,
              i: Replica
             ]
             \cup
             [type: {"COMMIT"}, 
              v: View,
              k: Op
             ]
             \cup
             \* State transfer.
             [type: {"GETSTATE"},
              v: View,
              n: Op
             ]
             \cup 
             [type: {"NEWSTATE"},
              v: View,
              l: [Op -> {Empty} \cup LogEntry],
              n: Op,
              k: Op
             ]
             \cup
             \* View change messages.
             [type: {"STARTVIEWCHANGE"},
              v: View,
              i: Replica
             ]
             \cup
             [type: {"DOVIEWCHANGE"},
              v: View,
              lastNormalV: View,
              n: Op,
              l: [Op -> {Empty} \cup LogEntry],
              k: Op,
              i: Replica
             ]
             \cup
             [type: {"StartView"},
              v: View,
              l: [Op -> {Empty} \cup LogEntry],
              n: Op,
              k: Op,
              i: Replica
             ]
             \* Recovery
             \cup
             [type: {"RECOVERY"},
              x: Replica \X Op,
              i: Replica
             ]
             \cup
             [type: {"RECOVERYRESPONSE"},
              v: View, 
              x: Replica \X Op, 
              l: [Op -> {Empty} \cup LogEntry], 
              n: Op, 
              k: Op,
              isPrimary: BOOLEAN
             ]

\* The type invariant.
TypeOk == /\ viewNum \in [Replica -> View]
          \* lastNormal not in paper.
          /\ lastNormal \in [Replica -> View]
          /\ opNum \in [Replica -> Op]
          /\ commitNum \in [Replica -> Op]
          /\ status \in [Replica -> {"normal", "view-change", "recovering"}]
          /\ log \in [Replica -> [Op -> {Empty} \cup LogEntry]]
          /\ clientTable \in [Replica -> [Client -> Op]]
          /\ clientRequest \in [Client -> Op]
          /\ nounce \in [Replica -> Replica \X Op]
          /\ msgs \subseteq Message

\* Safety property(non-inductive invariant) 
\* of view changes:
\* At any time of normal operation, 
\* logs are in sync op to a given commit.
ViewChangeOk == \A r1, r2 \in Replica:
                    (/\ viewNum[r1] = viewNum[r2] 
                     /\ commitNum[r1] = commitNum[r2]
                     /\ status[r1] = status[r2]
                     /\ status[r1] = "normal") =>
                         \A n \in 0..commitNum[r1]: 
                            /\ log[r1][n] = log[r2][n]

\* Stab at an inductive invariant implying
\* the safety propery of view changes.
\* "any operation o that committed in view 
\* v is known to at least f + 1 replicas"
IViewChangeOk == \A op \in Op: \E r \in Replica:
                    LET
                        quorum 
                            == {rr \in Replica: 
                                /\ commitNum[rr] >= op
                                /\ \A n \in 0..commitNum[r]: 
                                    /\ log[rr][n] = log[r][n]
                                }    
                    IN
                    /\ commitNum[r] >= op 
                        => Cardinality(quorum) >= F + 1
                           

\* Safety property of recovery.
\* We don't reset `lastNormal` on crash, 
\* so it can be used here for assertions.
\* Appears to be an inductive invariant,
\* adding a safety propety implied by it 
\* would require history variables, I think.
RecoveryOk == \A r \in Replica:
                LET
                    quorum == {rr \in Replica: 
                                /\ status[rr] = "normal" 
                                /\ viewNum[rr] >= lastNormal[r]}
                IN
                /\ status[r] = "recovering" => Cardinality(quorum) = F + 1           
-----------------------------------------------------------------------------

Init == /\ viewNum = [r \in Replica |->  0]
        /\ lastNormal = [r \in Replica |-> 0]
        /\ opNum = [r \in Replica |->  0]
        /\ commitNum = [r \in Replica |-> 0]
        /\ status = [r \in Replica |->  "normal"]
        /\ log = [r \in Replica |->  [op \in Op |-> Empty]]
        /\ clientTable = [r \in Replica |->  [c \in Client |-> 0]]
        /\ clientRequest = [c \in Client |-> 0]
        /\ nounce = [r \in Replica |->  <<r, 0>>]
        /\ msgs = {}

\* View Change: step 1. 
\* A replica notices the need for a view change,
\* based on its own timer(here modeled as simply "happening").
ReplacePrimary(r)==  /\ viewNum[r] < N
                     /\ status[r] = "normal"
                     /\ status' = [status EXCEPT ![r] = "view-change"]
                     /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                     /\ viewNum' = [viewNum EXCEPT ![r] = @ + 1]
                     /\ msgs' = msgs \cup 
                       [type: {"STARTVIEWCHANGE"},
                        v: {viewNum[r]'},
                        i: {r}
                       ]
                     /\ UNCHANGED<<opNum, 
                                log, commitNum, 
                                    clientTable, clientRequest, nounce>>

\* View Change: step 1.
\* A replica notices the need for a view change 
\* because it receives a DOVIEWCHANGE or a STARTVIEWCHANGE message.
NoticeViewChange(r) == \E msg \in msgs:
                            /\ msg.type \in {"DOVIEWCHANGE", "STARTVIEWCHANGE"}
                            /\ msg.i # r 
                            /\ msg.v > viewNum[r]
                            /\ status[r] = "normal"
                            /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                            /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                            /\ status' = [status EXCEPT ![r] = "view-change"]
                            /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {msg.v},
                                     i: {r}
                                    ]
                            /\ UNCHANGED<<opNum, 
                                                log, commitNum,
                                                clientTable, clientRequest, nounce>>

\* View Change: step 2.
\* When a replica receives STARTVIEWCHANGE messages 
\* for its view-number from f other replicas.
SendDoViewChange(r) == LET
                          startViewMsgs == {msg \in msgs: 
                                            /\ msg.type = "STARTVIEWCHANGE"
                                            /\ msg.v = viewNum[r]
                                            /\ msg.i # r}
                          hasQuorum == Cardinality(startViewMsgs) >= F
                       IN          
                       /\ status[r] = "view-change"
                       /\ msgs' = msgs \cup
                               [type: {"DOVIEWCHANGE"},
                                v: {viewNum[r]},
                                lastNormalV: {lastNormal[r]},
                                n: {opNum[r]},
                                l: {log[r]},
                                k: {commitNum[r]},
                                i: {r}
                               ]
                       /\ UNCHANGED<<viewNum, status, opNum, lastNormal,
                                            log, commitNum,
                                                clientTable, clientRequest, nounce>>
                            

\* View Change: step 3.
\* The primary receives DOVIEWCHANGE from f+1 replicas.
CompleteViewChange(r) == LET
                            MaxLog(S) == CHOOSE x \in S : \A y \in S : 
                                            \/ y.lastNormalV < x.lastNormalV 
                                            \/ /\ y.lastNormalV = x.lastNormalV 
                                               /\ y.n <= x.n
                            MaxCommitNum(S) == CHOOSE x \in S : \A y \in S : y.k <= x.k
                            doViewmsgs == {msg \in msgs: msg.type = "DOVIEWCHANGE" /\ msg.v = viewNum[r]}
                            hasQuorum == Cardinality(doViewmsgs) >= F+1
                            newLog == MaxLog(doViewmsgs).l
                            newLogTopOp == MaxLog(doViewmsgs).n
                            topOpNum == IF newLog[newLogTopOp] \in LogEntry 
                                            THEN newLog[newLogTopOp][2] 
                                        ELSE 1
                            newCommitNum == MaxCommitNum(doViewmsgs).k
                         IN
                         /\ IsPrimary(r)
                         /\ hasQuorum
                         /\ status[r] = "view-change"
                         /\ status' = [status EXCEPT ![r] = "normal"]
                         /\ commitNum' = [commitNum EXCEPT ![r] = newCommitNum]
                         /\ opNum' = [opNum EXCEPT ![r] = topOpNum]
                         /\ log' = [log EXCEPT ![r] = newLog]
                         /\ msgs' = msgs \cup
                                [type: {"StartView"},
                                 v: {viewNum[r]},
                                 l: {log[r]'},
                                 n: {opNum[r]'},
                                 k: {commitNum[r]'},
                                 i: {r}
                                ] 
                         /\ UNCHANGED<<clientTable, viewNum, clientRequest, lastNormal, nounce>>

\* View Change: step 5.
HandleStartView(r) == \E msg \in msgs:
                        /\ ~IsPrimary(r)
                        /\ msg.type = "StartView"
                        /\ status[r] = "view-change"
                        /\ msg.i # r
                        /\ msg.v = viewNum[r]
                        /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                        /\ status' = [status EXCEPT ![r] = "normal"]
                        /\ log' = [log EXCEPT ![r] = msg.l]
                        \* Note: execution and prepare of uncommitted
                        \* happens when relevant messages are handled after view change(I think).
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ opNum' = [opNum EXCEPT ![r] = msg.n]
                        /\ UNCHANGED<<msgs, clientTable, clientRequest, viewNum, nounce>>

\* Normal operation: Step 1.
SendRequest(client) == /\ clientRequest[client] < N
                       /\ clientRequest' = [clientRequest EXCEPT ![client] = @ + 1]
                       /\ msgs' = msgs \cup 
                            [type: {"REQUEST"}, 
                                clientId: {client}, 
                                requestNum: {clientRequest[client]'}]
                       /\ UNCHANGED<<viewNum, status, opNum, 
                                log, commitNum, clientTable, lastNormal, nounce>>

\* Normal operation: Step 2 and 3.
HandleRequest(r) == 
                    /\ status[r] = "normal"
                    /\ opNum[r] < N
                    /\ \E msg \in msgs:
                        /\ msg.type = "REQUEST"
                        /\ clientTable[r][msg.clientId] < N
                        /\ IsPrimary(r)
                        /\ msg.requestNum > clientTable[r][msg.clientId]
                        /\ opNum' = [opNum EXCEPT ![r] = @ + 1]
                        /\ log' = [log EXCEPT ![r][opNum[r]'] = <<msg.clientId, opNum[r]'>>]
                        /\ clientTable' = [clientTable EXCEPT ![r][msg.clientId] = @ + 1]
                        /\ msgs' = msgs \cup 
                            [type: {"PREPARE"}, 
                             v: {viewNum[r]},
                             m: {msg},
                             n: {opNum[r]'},
                             k: {commitNum[r]}
                            ]
                        /\ UNCHANGED<<viewNum, status, 
                                        commitNum, clientRequest, lastNormal, nounce>>

\* Normal operation: Step 4 and 7(new commit in prepare).
HandlePrepare(r) == /\ status[r] = "normal"
                    /\ \E msg \in msgs:
                        /\ msg.type = "PREPARE"
                        /\ msg.m.requestNum > clientTable[r][msg.m.clientId]
                        /\ ~IsPrimary(r)
                        /\ viewNum[r] = msg.v
                        /\ msg.n = opNum[r] + 1
                        /\ opNum' = [opNum EXCEPT ![r] = @ + 1]
                        \* Note previous commit.
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ log' = [log EXCEPT ![r][msg.n] = <<msg.m.clientId, opNum[r]'>>]
                        /\ clientTable' = [clientTable EXCEPT ![r][msg.m.clientId] = @ + 1]
                        /\ msgs' = msgs \cup 
                            [type: {"PREPAREOK"}, 
                             v: {viewNum[r]},
                             n: {opNum[r]'},
                             i: {r}
                            ]
                        /\ UNCHANGED<<viewNum, status, 
                                        clientRequest, lastNormal, nounce>>

\* Normal operation: Step 5.
\* TODO: client reply.
HandlePrepareOk(r) == LET
                         prepareOkmsgs == {msg \in msgs: 
                                            /\ msg.type = "PREPAREOK"
                                            /\ msg.v = viewNum[r]
                                            \* Ordering prepares in commit order.
                                            /\ msg.n = commitNum[r] + 1
                                            /\ msg.i # r }
                         hasQuorum == Cardinality(prepareOkmsgs) >= F
                      IN
                      /\ IsPrimary(r)
                      /\ status[r] = "normal"
                      /\ hasQuorum
                      /\ commitNum' = [commitNum EXCEPT ![r] = @ + 1]
                      /\ msgs' = msgs \cup 
                            [type: {"COMMIT"}, 
                             v: {viewNum[r]},
                             k: {commitNum[r]'}
                            ]
                      /\ UNCHANGED<<viewNum, status, 
                                        clientTable, log, opNum,
                                        clientRequest, lastNormal, nounce>>

\* Normal operation: Step 7.
HandleCommit(r) == /\ status[r] = "normal"
                   /\ \E msg \in msgs:
                        /\ ~IsPrimary(r)
                        /\ msg.type = "COMMIT"
                        /\ msg.v = viewNum[r]
                        /\ msg.k > commitNum[r]
                        /\ msg.k =< opNum[r]
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ UNCHANGED<<viewNum, status, opNum, log, 
                                msgs, clientTable, clientRequest, 
                                lastNormal, nounce>>

\* Start state transfer.
\* Using info in PREPARE messages(todo: other messages?)
\* Note: not switching approach on whether view or only opNum is outdated,
\* in both case updating entire log and state.
StartStateTransfer(r) == /\ \E msg \in msgs:
                            /\ msg.type = "PREPARE"
                            /\ \/ /\ msg.v = viewNum[r]
                                  /\ msg.n > opNum[r]
                               \/ /\ msg.v > viewNum[r]
                            /\ msgs' = msgs \cup 
                                [type: {"GETSTATE"},
                                 v: IF msg.v > viewNum[r] THEN {msg.v} ELSE {viewNum[r]},
                                 n: {opNum[r]}
                                ]
                            /\ UNCHANGED<<viewNum, status, opNum, log, commitNum, 
                                                        clientTable, clientRequest, 
                                                            lastNormal, nounce>>

\* A replica responds to a GETSTATE message
HandleGetState(r) == /\ status[r] = "normal"
                     /\ \E msg \in msgs:
                        /\ msg.type = "GETSTATE"
                        /\ msg.v = viewNum[r]
                        /\ msgs' = msgs \cup
                            [type: {"NEWSTATE"},
                             v: {viewNum[r]},
                             l: {log[r]},
                             n: {opNum[r]},
                             k: {commitNum[r]}
                            ]
                        /\ UNCHANGED<<viewNum, status, opNum, log, commitNum, 
                                                        clientTable, clientRequest, 
                                                            lastNormal, nounce>>

\* A replica receives a NEWSTATE message
HandleNewState(r) == /\ status[r] = "normal"
                     /\ \E msg \in msgs:
                        /\ msg.type = "NEWSTATE"
                        /\ \/ /\ msg.v > viewNum[r]
                           \/ /\ msg.v = viewNum[r]
                              /\ msg.n > opNum[r]
                        /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                        /\ opNum' = [opNum EXCEPT ![r] = msg.n]
                        /\ log' = [log EXCEPT ![r] = msg.l]
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ UNCHANGED<<status, msgs, clientTable, clientRequest, 
                                            lastNormal, nounce>>                   

\* Start Recovery
StartRecovery(r) == 
              /\ nounce[r][2] < N
              /\ status[r] = "recovering"
              /\ nounce' = [nounce EXCEPT ![r] = <<@[1], @[2] + 1>>]
              /\ msgs' = msgs \cup
                        [type: {"RECOVERY"},
                         x: {nounce'[r]},
                         i: {r}
                        ]
              /\ UNCHANGED<<viewNum, status, opNum, log, commitNum, 
                                clientTable, clientRequest, 
                                lastNormal>>

\* Respond to recovery
HandleRecoveryRequest(r) == 
                     /\ status[r] = "normal"
                     /\ \E msg \in msgs:
                        /\ msg.type = "RECOVERY"
                        /\ msgs' = msgs \cup
                            [type: {"RECOVERYRESPONSE"},
                             v: {viewNum[r]}, 
                             x: {msg.x}, 
                             l: {log[r]}, 
                             n: {opNum[r]}, 
                             k: {commitNum[r]},
                             isPrimary: {IsPrimary(r)}
                            ]
                        /\ UNCHANGED<<viewNum, status, opNum, log, commitNum, 
                                clientTable, clientRequest, 
                                lastNormal, nounce>>

\* Recovery completed
Recover(r) == LET
                MaxView(S) == CHOOSE x \in S : \A y \in S : y.v <= x.v
                responses == {msg \in msgs: /\ msg.type = "RECOVERYRESPONSE" 
                                            /\ msg.x = nounce[r]}
                primaryResponses == {msg \in responses: msg.isPrimary /\ msg.v = MaxView(responses).v}
                canRecover == Cardinality(responses) >= F+1 /\ Cardinality(primaryResponses) = 1
                info == IF canRecover THEN CHOOSE x \in primaryResponses: TRUE ELSE FALSE
              IN  
              /\ status[r] = "recovering"
              /\ canRecover
              /\ viewNum' = [viewNum EXCEPT ![r] = info.v]
              /\ log' = [log EXCEPT ![r] = info.l]
              /\ opNum' = [opNum EXCEPT ![r] = info.n]
              /\ commitNum' = [commitNum EXCEPT ![r] = info.k]
              /\ status' = [status EXCEPT ![r] = "normal"]
              /\ lastNormal' = [lastNormal EXCEPT ![r] = info.v]
              /\ UNCHANGED<<msgs, clientTable, clientRequest, nounce>>

\* Assumption: only F simultaneous failure, as per the paper: 
\* "the protocol is live, assuming no more that f replicas fail simultaneously."
Crash(r) == /\ Cardinality({rr \in Replica: status[rr] = "recovering"}) \in {0, F}
            /\ nounce[r][2] < N
            /\ status[r] \notin {"recovering"}
            /\ status' = [status EXCEPT ![r] = "recovering"]
            /\ UNCHANGED<<viewNum, opNum, log, commitNum, 
                                msgs, clientTable, clientRequest, 
                                lastNormal, nounce>>

Next == \/ \E c \in Client: 
            \/ SendRequest(c)
        \/ \E r \in Replica:
            \/ HandleRequest(r)
            \/ HandlePrepare(r)
            \/ NoticeViewChange(r)
            \/ SendDoViewChange(r)
            \/ CompleteViewChange(r)
            \/ HandleStartView(r)
            \/ HandlePrepareOk(r)
            \/ HandleCommit(r)
            \/ ReplacePrimary(r)
            \/ StartStateTransfer(r)
            \/ HandleGetState(r)
            \/ HandleNewState(r)
            \/ StartRecovery(r)
            \/ HandleRecoveryRequest(r)
            \/ Recover(r)
            \/ Crash(r)

Spec  ==  Init  /\  [][Next]_<<viewNum, status, opNum, log, commitNum, 
                                msgs, clientTable, clientRequest, 
                                lastNormal, nounce>>
============================================================================
THEOREM  Spec  =>  [](TypeOk /\ ViewChangeOk /\ IViewChangeOk /\ RecoveryOk)
=============================================================================

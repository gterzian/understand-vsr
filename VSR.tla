-------------------------------- MODULE VSR --------------------------------
EXTENDS FiniteSets, Naturals
VARIABLE viewNum, status, opNum, log, commitNum, 
            msgs, clientTable, clientRequest, primary, lastNormal
CONSTANT N, Empty, F
----------------------------------------------------------------------------

Replica == 0..N
Client == 0..N
View == 0..N
Op == 0..N
LogEntry == Client \X Op
ASSUME Empty \notin LogEntry

Message == [type: {"REQUEST"}, 
            clientId: Client, 
            requestNum: Op,
            primary: Replica,
            v: View]
            \cup 
            [type: {"PREPARE"},
             v: View,
             m: [type: {"REQUEST"}, 
                 clientId: Client, 
                 requestNum: Op,
                 primary: Replica,
                 v: View],
             n: Op,
             k: Op,
             primary: Replica
             ]
             \cup
             [type: {"PREPAREOK"}, 
              v: View,
              n: Op,
              i: Replica,
              primary: Replica
             ]
             \cup
             [type: {"COMMIT"}, 
              v: View,
              k: Op
             ]
             \* View change messages.
             \cup
             [type: {"STARTVIEWCHANGE"},
              v: View,
              i: Replica,
              primary: Replica
             ]
             \cup
             [type: {"DOVIEWCHANGE"},
              v: View,
              lastNormalV: View,
              n: Op,
              l: [Op -> {Empty} \cup LogEntry],
              k: Op,
              i: Replica,
              primary: Replica
             ]
             \cup
             [type: {"StartView"},
              v: View,
              l: [Op -> {Empty} \cup LogEntry],
              n: Op,
              k: Op,
              i: Replica
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
          /\ msgs \subseteq Message
          /\ primary \in Replica

\* Safety property of view changes.
ViewChangeOk == \A r1, r2 \in Client:
                    (/\ viewNum[r1] = viewNum[r2] 
                     /\ commitNum[r1] = commitNum[r2]
                     /\ commitNum[r1] > 0
                     /\ status[r1] = status[r2]
                     /\ status[r1] = "normal") =>
                         \A n \in 0..commitNum[r1]: 
                            /\ log[r1][n] = log[r2][n]
-----------------------------------------------------------------------------

Init == /\ viewNum = [r \in Replica |->  0]
        /\ lastNormal = [r \in Replica |->  0]
        /\ opNum = [r \in Replica |->  0]
        /\ commitNum = [r \in Replica |-> 0]
        /\ status = [r \in Replica |->  "normal"]
        /\ log = [r \in Replica |->  [op \in Op |-> Empty]]
        /\ clientTable = [r \in Replica |->  [c \in Client |-> 0]]
        /\ clientRequest = [c \in Client |-> 0]
        /\ msgs = {}
        /\ primary = CHOOSE x \in Replica: TRUE

\* View Change: step 1. 
\* A replica(from) notices the need for a view change,
\* based on its own timer, 
\* here modeled as a switch of the primary.
\* Note: can the new primary be the replica noticing the need for a change?
ReplacePrimary(r)==  /\ r # primary
                     /\ viewNum[r] < N
                     /\ status[r] = "normal"
                     /\ primary' = CHOOSE x \in Replica \ {primary}: TRUE
                     /\ status' = [status EXCEPT ![r] = "view-change"]
                     /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                  \* A replica i that notices the need 
                  \* for a view change advances its view-number.
                  \* But, see step 3, where the primary 
                  \* selects its view-number to that in the messages.
                  \* What if the primary is "r"?
                     /\ viewNum' = [viewNum EXCEPT ![r] = @ + 1]
                     /\ msgs' = msgs \cup 
                       [type: {"STARTVIEWCHANGE"},
                        v: {viewNum[r]'},
                        i: {r},
                        primary: {primary'}
                       ]
                     /\ UNCHANGED<<opNum, 
                                log, commitNum, 
                                    clientTable, clientRequest>>

\* View Change: step 1.
\* A replica notices the need for a view change 
\* because it receives a STARTVIEWCHANGE message.
\* Note: viewNum left unchanged.
HandleStartViewChange(r) == \E msg \in msgs:
                                /\ msg.type = "STARTVIEWCHANGE"
                                /\ msg.i # r
                                /\ msg.v > viewNum[r]
                                /\ status[r] = "normal"
                                /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                                /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                                /\ status' = [status EXCEPT ![r] = "view-change"]
                                /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {msg.v},
                                     i: {r},
                                     primary: {msg.primary}
                                    ]
                                /\ UNCHANGED<<primary, opNum, 
                                                log, commitNum, 
                                                clientTable, clientRequest>>

\* View Change: step 1.
\* A replica notices the need for a view change 
\* because it receives a DOVIEWCHANGE message.
\* Note: viewNum left unchanged.
HandleDoViewChange(r) == \E msg \in msgs:
                            /\ msg.type = "DOVIEWCHANGE"
                            /\ msg.i # r 
                            /\ msg.v > viewNum[r]
                            /\ status[r] = "normal"
                            /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                            /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                            /\ status' = [status EXCEPT ![r] = "view-change"]
                            /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {msg.v},
                                     i: {r},
                                     primary: {msg.primary}
                                    ]
                            /\ UNCHANGED<<primary, opNum, 
                                                log, commitNum,
                                                clientTable, clientRequest>>

\* View Change: step 2.
\* When a replica receives STARTVIEWCHANGE messages 
\* for its view-number from f other replicas.
SendDoViewChange(r) == \E rr \in Replica:
                       LET
                          startViewMsgs == {msg \in msgs: 
                                            /\ msg.type = "STARTVIEWCHANGE"
                                            /\ msg.v = viewNum[r]
                                            /\ msg.i # r
                                            /\ msg.primary = rr}
                          hasQuorum == Cardinality(startViewMsgs) >= F
                          didNotSendYet == Cardinality({msg \in msgs: 
                                                        /\ msg.type = "DOVIEWCHANGE"
                                                        /\ msg.v = viewNum[r]
                                                        /\ msg.i = r
                                                        /\ msg.primary = rr}) = 0
                       IN 
                       /\ didNotSendYet         
                       /\ status[r] = "view-change"
                       /\ msgs' = msgs \cup
                               [type: {"DOVIEWCHANGE"},
                                v: {viewNum[r]},
                                lastNormalV: {lastNormal[r]},
                                n: {opNum[r]},
                                l: {log[r]},
                                k: {commitNum[r]},
                                i: {r},
                                primary: {rr}
                               ]
                       /\ UNCHANGED<<viewNum, status, opNum, lastNormal,
                                            log, commitNum,
                                                clientTable, clientRequest, primary>>
                            

\* View Change: step 3.
\* The primary receives DOVIEWCHANGE from f+1 replicas.
CompleteViewChange(r) == LET
                            MaxLog(S) == CHOOSE x \in S : \A y \in S : 
                                            \/ y.lastNormalV < x.lastNormalV 
                                            \/ /\ y.lastNormalV = x.lastNormalV 
                                               /\ y.n <= x.n
                            MaxCommitNum(S) == CHOOSE x \in S : \A y \in S : y.k <= x.k
                            doViewmsgs == {msg \in msgs: 
                                            /\ msg.type = "DOVIEWCHANGE"
                                            /\ msg.v = viewNum[r]
                                            /\ msg.primary = r}
                            hasQuorum == Cardinality(doViewmsgs) >= F+1
                            newLog == MaxLog(doViewmsgs).l
                            newLogTopOp == MaxLog(doViewmsgs).n
                            topOpNum == IF newLog[newLogTopOp] \in LogEntry 
                                            THEN newLog[newLogTopOp][2] 
                                        ELSE 0
                            newCommitNum == MaxCommitNum(doViewmsgs).k
                         IN
                         /\ hasQuorum
                         /\ status[r] = "view-change"
                         /\ status' = [status EXCEPT ![r] = "normal"]
                         \*/\ viewNum' = [viewNum EXCEPT ![r] = @ + 1]
                         \*/\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
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
                         /\ UNCHANGED<<clientTable, clientRequest, lastNormal, viewNum, primary>>
\* View Change: step 5.
HandleStartView(r) == \E msg \in msgs:
                        /\ primary # r
                        /\ msg.type = "StartView"
                        /\ status[r] = "view-change"
                        /\ msg.i # r 
                        /\ msg.v = viewNum[r]
                        /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                        /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]']
                        /\ status' = [status EXCEPT ![r] = "normal"]
                        /\ log' = [log EXCEPT ![r] = msg.l]
                        \* TODO: execute and prepare uncommitted.
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ opNum' = [opNum EXCEPT ![r] = msg.n]
                        /\ UNCHANGED<<msgs, clientTable, clientRequest, primary>>

\* Normal operation: Step 1.
SendRequest(client) == /\ clientRequest[client] < N
                       /\ clientRequest' = [clientRequest EXCEPT ![client] = @ + 1]
                       /\ msgs' = msgs \cup 
                            [type: {"REQUEST"}, 
                                clientId: {client}, 
                                requestNum: {clientRequest[client]'},
                                primary: {primary},
                                v: {viewNum[primary]}]
                       /\ UNCHANGED<<primary, viewNum, status, opNum, 
                                log, commitNum, clientTable, lastNormal>>

\* Normal operation: Step 2 and 3.
HandleRequest(r) == /\ r = primary
                    /\ status[r] = "normal"
                    /\ opNum[r] < N
                    /\ \E msg \in msgs:
                        /\ msg.type = "REQUEST"
                        /\ msg.primary = r
                        \*/\ msg.v = viewNum[r]
                        /\ msg.requestNum > clientTable[r][msg.clientId]
                        /\ opNum' = [opNum EXCEPT ![r] = @ + 1]
                        /\ log' = [log EXCEPT ![r][opNum[r]'] = <<msg.clientId, opNum[r]'>>]
                        /\ clientTable' = [clientTable EXCEPT ![r][msg.clientId] = @ + 1]
                        /\ msgs' = msgs \cup 
                            [type: {"PREPARE"}, 
                             v: {viewNum[r]},
                             m: {msg},
                             n: {opNum[r]'},
                             k: {commitNum[r]},
                             primary: {r}
                            ]
                        /\ UNCHANGED<<primary, viewNum, status, 
                                        commitNum, clientRequest, lastNormal>>

\* Normal operation: Step 4 and 7(new commit in prepare).
HandlePrepare(r) == /\ r # primary
                    /\ status[r] = "normal"
                    /\ \E msg \in msgs:
                        /\ msg.type = "PREPARE"
                        /\ msg.v = viewNum[r]
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
                             i: {r},
                             primary: {msg.primary}
                            ]
                        /\ UNCHANGED<<primary, viewNum, status, 
                                        clientRequest, lastNormal>>

\* Normal operation: Step 5.
\* Note: not clear how to handle concurrent ongoing prepares: The primary waits for...
\* TODO: client reply.
HandlePrepareOk(r) == LET
                         prepareOkmsgs == {msg \in msgs: 
                                            /\ msg.type = "PREPAREOK"
                                            /\ msg.v = viewNum[r]
                                            \* Ordering prepares in commit order.
                                            /\ msg.n = commitNum[r] + 1
                                            /\ msg.primary = r
                                            /\ msg.i # r }
                         hasQuorum == Cardinality(prepareOkmsgs) >= F
                      IN
                      /\ r = primary
                      /\ status[r] = "normal"
                      /\ hasQuorum
                      /\ commitNum' = [commitNum EXCEPT ![r] = @ + 1]
                      /\ msgs' = msgs \cup 
                            [type: {"COMMIT"}, 
                             v: {viewNum[r]},
                             k: {commitNum[r]'}
                            ]
                      /\ UNCHANGED<<primary, viewNum, status, 
                                        clientTable, log, opNum,
                                        clientRequest, lastNormal>>

\* Normal operation: Step 7.
HandleCommit(r) == /\ r # primary
                    /\ status[r] = "normal"
                    /\ \E msg \in msgs:
                        /\ msg.type = "COMMIT"
                        /\ msg.v = viewNum[r]
                        /\ msg.k < commitNum[r]
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ UNCHANGED<<viewNum, status, opNum, log, 
                                msgs, clientTable, clientRequest, 
                                primary, lastNormal>>

Next == \/ \E c \in Client: 
            \/ SendRequest(c)
        \/ \E r \in Replica:
            \/ HandleRequest(r)
            \/ HandlePrepare(r)
            \/ HandleStartViewChange(r)
            \/ SendDoViewChange(r)
            \/ HandleDoViewChange(r)
            \/ CompleteViewChange(r)
            \/ HandleStartView(r)
            \/ HandlePrepareOk(r)
            \/ HandleCommit(r)
            \/ ReplacePrimary(r)

Spec  ==  Init  /\  [][Next]_<<viewNum, status, opNum, log, commitNum, 
                                msgs, clientTable, clientRequest, 
                                primary, lastNormal>>
============================================================================
THEOREM  Spec  =>  [](TypeOk /\ ViewChangeOk)
=============================================================================

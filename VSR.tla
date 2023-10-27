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
            requestNum: Op]
            \cup 
            [type: {"PREPARE"},
             v: View,
             m: [type: {"REQUEST"}, 
                clientId: Client, 
                requestNum: Op],
             n: Op,
             k: Op
             ]
             \* View change messages.
             \cup
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
ReplacePrimary == LET
                    from == CHOOSE x \in Replica \ {primary}: TRUE
                  IN
                  /\ viewNum[from] < N
                  /\ primary' = CHOOSE x \in Replica \ {primary, from}: TRUE
                  /\ status' = [status EXCEPT ![from] = "view-change"]
                  /\ lastNormal' = [lastNormal EXCEPT ![from] = viewNum[from]]
                  \* A replica i that notices the need 
                  \* for a view change advances its view-number.
                  \* But, see step 3, where the primary 
                  \* selects its view-number to that in the messages.
                  \* What if the primary is "from"?
                  /\ viewNum' = [viewNum EXCEPT ![from] = @ + 1]
                  /\ msgs' = msgs \cup 
                    [type: {"STARTVIEWCHANGE"},
                     v: {viewNum[from]'},
                     i: {from}
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
                                /\ status[r] # "view-change"
                                /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                                /\ status' = [status EXCEPT ![r] = "view-change"]
                                /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {msg.v},
                                     i: {r}
                                    ]
                                /\ UNCHANGED<<primary, opNum, 
                                                log, commitNum, viewNum,
                                                clientTable, clientRequest>>

\* View Change: step 1.
\* A replica notices the need for a view change 
\* because it receives a DOVIEWCHANGE message.
\* Note: viewNum left unchanged.
HandleDoViewChange(r) == \E msg \in msgs:
                            /\ msg.type = "DOVIEWCHANGE"
                            /\ msg.i # r 
                            /\ msg.v > viewNum[r]
                            /\ status[r] # "view-change"
                            /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]]
                            /\ status' = [status EXCEPT ![r] = "view-change"]
                            /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {msg.v},
                                     i: {r}
                                    ]
                            /\ UNCHANGED<<primary, opNum, 
                                                log, commitNum, viewNum,
                                                clientTable, clientRequest>>

\* View Change: step 2.
\* When a replicareceives STARTVIEWCHANGE messages 
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
                                            /\ msg.v = viewNum[r] + 1}
                            hasQuorum == Cardinality(doViewmsgs) >= F+1
                            newLog == MaxLog(doViewmsgs).l
                            TopEntry(S) == CHOOSE x \in S : \A y \in S : y <= x
                            topOpNum == IF newLog[TopEntry(Op)] \in LogEntry 
                                            THEN newLog[TopEntry(Op)][2] 
                                        ELSE 0
                            newCommitNum == MaxCommitNum(doViewmsgs).k
                         IN
                         /\ hasQuorum
                         /\ r = primary
                         /\ status[r] = "view-change"
                         /\ status' = [status EXCEPT ![r] = "normal"]
                         /\ viewNum' = [viewNum EXCEPT ![r] = @ + 1]
                         /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]']
                         /\ commitNum' = [commitNum EXCEPT ![r] = newCommitNum]
                         /\ opNum' = [opNum EXCEPT ![r] = topOpNum]
                         /\ log' = [log EXCEPT ![r] = newLog]
                         /\ msgs' = msgs \cup
                                [type: {"StartView"},
                                 v: {viewNum[r]'},
                                 l: {log[r]'},
                                 n: {opNum[r]'},
                                 k: {commitNum[r]'},
                                 i: {r}
                                ] 
                         /\ UNCHANGED<<clientTable, clientRequest, primary>>

HandleStartView(r) == \E msg \in msgs:
                        /\ primary # r
                        /\ msg.type = "StartView"
                        /\ status[r] = "view-change"
                        /\ msg.i # r 
                        /\ msg.v > viewNum[r]
                        /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                        /\ lastNormal' = [lastNormal EXCEPT ![r] = viewNum[r]']
                        /\ status' = [status EXCEPT ![r] = "normal"]
                        /\ log' = [log EXCEPT ![r] = msg.l]
                        \* TODO: execute and prepare uncommitted.
                        /\ commitNum' = [commitNum EXCEPT ![r] = msg.k]
                        /\ opNum' = [opNum EXCEPT ![r] = msg.n]
                        /\ UNCHANGED<<msgs, clientTable, clientRequest, primary>>

SendRequest(client) == /\ clientRequest[client] < N
                       /\ clientRequest' = [clientRequest EXCEPT ![client] = @ + 1]
                       /\ msgs' = msgs \cup 
                            [type: {"REQUEST"}, 
                                clientId: {client}, 
                                requestNum: {clientRequest[client]'}]
                       /\ UNCHANGED<<primary, viewNum, status, opNum, 
                                log, commitNum, clientTable, lastNormal>>

HandleRequest(r) == /\ r = primary
                    /\ status[r] = "normal"
                    /\ opNum[r] < N
                    /\ \E msg \in msgs:
                        /\ msg.type = "REQUEST"
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
                        /\ UNCHANGED<<primary, viewNum, status, 
                                        commitNum, clientRequest, lastNormal>>

Next == \/ \E c \in Client: 
            \/ SendRequest(c)
        \/ \E r \in Replica:
            \/ HandleRequest(r)
            \/ HandleStartViewChange(r)
            \/ SendDoViewChange(r)
            \/ HandleDoViewChange(r)
            \/ CompleteViewChange(r)
            \/ HandleStartView(r)
        \/ ReplacePrimary

Spec  ==  Init  /\  [][Next]_<<viewNum, status, opNum, 
                                log, commitNum, msgs, 
                                    clientTable, clientRequest, primary>>
============================================================================
THEOREM  Spec  =>  [](TypeOk)
=============================================================================
\* Modification History
\* Last modified Fri Oct 27 13:50:47 CST 2023 by Gregory
\* Created Wed Oct 25 15:47:58 CST 2023 by Gregory

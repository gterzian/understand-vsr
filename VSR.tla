-------------------------------- MODULE VSR --------------------------------
EXTENDS FiniteSets, Naturals
VARIABLE viewNum, status, opNum, log, commitNum, msgs, clientTable, clientRequest, primary
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
              k: Op
             ]

\* The type invariant.
TypeOk == /\ viewNum \in [Replica -> View]
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
        /\ opNum = [r \in Replica |->  0]
        /\ commitNum = [r \in Replica |-> 0]
        /\ status = [r \in Replica |->  "normal"]
        /\ log = [r \in Replica |->  [op \in Op |-> Empty]]
        /\ clientTable = [r \in Replica |->  [c \in Client |-> 0]]
        /\ clientRequest = [c \in Client |-> 0]
        /\ msgs = {}
        /\ primary = CHOOSE x \in Replica: TRUE

ReplacePrimary == LET
                    from == CHOOSE x \in Replica \ {primary}: TRUE
                  IN
                  /\ viewNum[from] < N
                  /\ primary' = CHOOSE x \in Replica \ {primary, from}: TRUE
                  /\ status' = [status EXCEPT ![from] = "view-change"]
                  /\ viewNum' = [viewNum EXCEPT ![from] = @ + 1]
                  /\ msgs' = msgs \cup 
                    [type: {"STARTVIEWCHANGE"},
                     v: {viewNum[from]'},
                     i: {from}
                    ]
                  /\ UNCHANGED<<opNum, 
                                log, commitNum, 
                                    clientTable, clientRequest>>

HandleStartViewChange(r) == \E msg \in msgs:
                                /\ msg.type = "STARTVIEWCHANGE"
                                /\ msg.i # r
                                /\ msg.v > viewNum[r]
                                /\ status[r] # "view-change"
                                /\ status' = [status EXCEPT ![r] = "view-change"]
                                /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                                /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {viewNum[r]'},
                                     i: {r}
                                    ]
                                /\ UNCHANGED<<primary, opNum, 
                                                log, commitNum, 
                                                clientTable, clientRequest>>

SendDoViewChange(r) == \E msg \in msgs:
                            /\ msg.type = "STARTVIEWCHANGE"
                            /\ msg.i # r
                            /\ status[r] = "view-change"
                            /\ msg.v = viewNum[r]
                            /\ msgs' = msgs \cup
                               [type: {"DOVIEWCHANGE"},
                                v: {viewNum[r]},
                                lastNormalV: {viewNum[r] - 1},
                                n: {opNum[r]},
                                l: {log[r]},
                                k: {commitNum[r]},
                                i: {r}
                               ]
                            /\ UNCHANGED<<viewNum, status, opNum, 
                                            log, commitNum,
                                                clientTable, clientRequest, primary>>
HandleDoViewChange(r) == \E msg \in msgs:
                            /\ msg.type = "DOVIEWCHANGE"
                            /\ msg.i # r 
                            /\ msg.v > viewNum[r]
                            /\ status[r] # "view-change"
                            /\ status' = [status EXCEPT ![r] = "view-change"]
                            /\ viewNum' = [viewNum EXCEPT ![r] = msg.v]
                            /\ msgs' = msgs \cup
                                    [type: {"STARTVIEWCHANGE"},
                                     v: {viewNum[r]'},
                                     i: {r}
                                    ]
                            /\ UNCHANGED<<primary, opNum, 
                                                log, commitNum, 
                                                clientTable, clientRequest>>

CompleteViewChange(r) == LET
                            MaxLog(S) == CHOOSE x \in S : \A y \in S : y.lastNormalV <= x.lastNormalV /\ y.n <= x.n
                            
                            MaxCommitNum(S) == CHOOSE x \in S : \A y \in S : y.k <= x.k
                            doViewmsgs == {msg \in msgs: 
                                            /\ msg.type = "DOVIEWCHANGE"
                                            /\ msg.v > viewNum[r]}
                            hasQuorum == Cardinality(doViewmsgs) >= F+1
                            newLog == MaxLog(doViewmsgs).l
                            TopEntry(S) == CHOOSE x \in S : \A y \in S : y <= x
                            topOpNum == IF newLog[TopEntry(Op)] \in LogEntry THEN newLog[TopEntry(Op)][2] ELSE 0
                            newCommitNum == MaxCommitNum(doViewmsgs).k
                         IN
                         /\ hasQuorum
                         /\ r = primary
                         /\ status[r] = "view-change"
                         /\ status' = [status EXCEPT ![r] = "normal"]
                         /\ viewNum' = [viewNum EXCEPT ![r] = @ + 1]
                         /\ commitNum' = [commitNum EXCEPT ![r] = newCommitNum]
                         /\ opNum' = [opNum EXCEPT ![r] = topOpNum]
                         /\ log' = [log EXCEPT ![r] = newLog]
                         /\ msgs' = msgs \cup
                                [type: {"StartView"},
                                 v: {viewNum[r]'},
                                 l: {log[r]'},
                                 n: {opNum[r]'},
                                 k: {commitNum[r]'}
                                ] 
                         /\ UNCHANGED<<clientTable, clientRequest, primary>>

SendRequest(client) == /\ clientRequest[client] < N
                       /\ clientRequest' = [clientRequest EXCEPT ![client] = @ + 1]
                       /\ msgs' = msgs \cup 
                            [type: {"REQUEST"}, 
                                clientId: {client}, 
                                requestNum: {clientRequest[client]'}]
                       /\ UNCHANGED<<primary, viewNum, status, opNum, 
                                log, commitNum, clientTable>>

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
                        /\ UNCHANGED<<primary, viewNum, status, commitNum, clientRequest>>

Next == \/ \E c \in Client: 
            \/ SendRequest(c)
        \/ \E r \in Replica:
            \/ HandleRequest(r)
            \/ HandleStartViewChange(r)
            \/ SendDoViewChange(r)
            \/ HandleDoViewChange(r)
            \/ CompleteViewChange(r)
        \/ ReplacePrimary

Spec  ==  Init  /\  [][Next]_<<viewNum, status, opNum, 
                                log, commitNum, msgs, 
                                    clientTable, clientRequest, primary>>
============================================================================
THEOREM  Spec  =>  [](TypeOk)
=============================================================================
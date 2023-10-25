-------------------------------- MODULE VSR --------------------------------
EXTENDS FiniteSets, Naturals
VARIABLE viewNum, status, opNum, log, commitNum, msgs, clientTable, clientRequest, primary
CONSTANT N, Empty
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

ReplacePrimary == /\ primary' = CHOOSE x \in Replica \ {primary}: TRUE
                  /\ UNCHANGED<<viewNum, status, opNum, 
                                log, commitNum, msgs, 
                                    clientTable, clientRequest>>

SendRequest(client) == /\ clientRequest[client] < N
                       /\ clientRequest' = [clientRequest EXCEPT ![client] = @ + 1]
                       /\ msgs' = msgs \cup 
                            [type: {"REQUEST"}, 
                                clientId: {client}, 
                                requestNum: {clientRequest[client]'}]
                       /\ UNCHANGED<<primary, viewNum, status, opNum, 
                                log, commitNum, clientTable>>

HandleRequest(r) == /\ r = primary
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
        \/ ReplacePrimary

Spec  ==  Init  /\  [][Next]_<<viewNum, status, opNum, 
                                log, commitNum, msgs, 
                                    clientTable, clientRequest, primary>>
============================================================================
THEOREM  Spec  =>  [](TypeOk)
=============================================================================
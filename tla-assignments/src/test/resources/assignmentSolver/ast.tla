------------------------------ MODULE ast ------------------------------
EXTENDS Integers(*, TLC*)

(*
CONSTANTS Proc, NULL, root, nbrs
ASSUME NULL \notin Proc /\ nbrs \in [Proc -> [Proc -> BOOLEAN]]
*)

N == 4
Proc == 1..N
NULL == 0
root == 1
nbrs == [p \in Proc |-> [q \in Proc |-> p < q]]

VARIABLES parent, reported, sntMsg
vars == <<parent, reported, sntMsg>> 
             
Init == /\ parent = [i \in Proc |-> NULL]
        /\ reported = [i \in Proc |-> FALSE]
        /\ sntMsg = [i \in Proc |-> [j \in Proc |-> FALSE]]

CanSend(i, j) ==  nbrs[i][j] /\ (i = root \/ parent[i] # NULL)
 
Update(i, j) == /\ parent' = [parent EXCEPT ![i] = j]
                /\ UNCHANGED <<reported, sntMsg>>

Send(i) == \E k \in Proc: /\ CanSend(i, k) /\ ~sntMsg[i][k]
                          /\ sntMsg' = [sntMsg EXCEPT ![i][k] = TRUE]
                          /\ UNCHANGED <<parent, reported>>
                                                                                    
Parent(i) == /\ parent[i] # NULL /\ ~reported[i]
             /\ reported' = [reported EXCEPT ![i] = TRUE] 
             /\ UNCHANGED <<sntMsg, parent>>
             
Next == \E i, j \in Proc: IF i # root /\ parent[i] = NULL /\ sntMsg[j][i]
                          THEN Update(i, j)
                          ELSE \/ Send(i) \/ Parent(i) 
                               \/ UNCHANGED <<parent, sntMsg, reported>>
                                                                            
Spec == /\ Init /\ [][Next]_vars 
        /\ WF_vars(\E i, j \in Proc: IF i # root /\ parent[i] = NULL /\ sntMsg[j][i]
                          THEN Update(i, j)
                          ELSE \/ Send(i) \/ Parent(i) 
                               \/ UNCHANGED <<parent, sntMsg, reported>>)
                                           
TypeOK == /\ \A i \in Proc : parent[i] = NULL \/ nbrs[i][parent[i]]             
          /\ reported \in [Proc -> BOOLEAN]  
          /\ sntMsg \in [Proc -> [Proc -> BOOLEAN]]
  
SpanningTree == <>(\A i \in Proc : i = root \/ (parent[i] # NULL /\ nbrs[i][parent[i]]))

OneParent == [][\A i \in Proc : parent[i] # NULL => parent[i] = parent'[i]]_vars

SntMsg == \A i \in Proc: (i # root /\ parent[i] = NULL => \A j \in Proc: ~sntMsg[i][j])
=============================================================================

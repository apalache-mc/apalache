------------------------------ MODULE bcastByzTyped ------------------------------

EXTENDS Naturals, FiniteSets

N == 4
T == 1
F == 1

VARIABLE 
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,
    \* @type: Set(<<Int, Str>>);
    sent

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
\* ASSUME (N > 3 * T) /\ (T >= F) /\ (F >= 0)

P == 1 .. N                 (* all processess, including the faulty ones    *)
Corr == 1 .. N - F          (* correct processes                            *)
Faulty == N - F + 1 .. N    (* the faulty processes                         *)

M == { "ECHO" }

vars == << pc, rcvd, sent >>

Receive(self) ==
        \E m \in sent \union { <<p, "ECHO">> : p \in Faulty }:
            /\ m \notin rcvd[self]
            /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] \union {m} ]

UponV1(self) ==
        /\ pc[self] = "V1"
        /\ pc' = [pc EXCEPT ![self] = "SE"]
        /\ sent' = sent \union { <<self, "ECHO">> }
        
UponNonFaulty(self) ==
        /\ pc[self] /= "SE"
        /\ Cardinality(rcvd'[self]) >= T + 1
        /\ Cardinality(rcvd'[self]) < N - T
        /\ pc' = [pc EXCEPT ![self] = "SE"]
        /\ sent' = sent \union { <<self, "ECHO">> }
        
UponAcceptNotSent(self) ==
        /\ (pc[self] \in { "V0", "V1" })
        /\ Cardinality(rcvd'[self]) >= N - T
        /\ pc' = [pc EXCEPT ![self] = "AC"]
        /\ sent' = sent \union { <<self, "ECHO">> }
        
UponAccept(self) ==
        /\ pc[self] = "SE"
        /\ Cardinality(rcvd'[self]) >= N - T
        /\ pc' = [pc EXCEPT ![self] = "AC"]
        /\ sent' = sent
        
Step(self) ==   /\ Receive(self)
                /\ \/ UponV1(self)
                   \/ UponNonFaulty(self)
                   \/ UponAcceptNotSent(self)
                   \/ UponAccept(self)
                   \/ pc' = pc /\ sent' = sent

Init == /\ sent = {}
        /\ pc = [ i \in Corr |-> "V1" ]
        \* /\ pc \in [ Corr -> {"V0", "V1"} ]
        /\ rcvd = [ i \in Corr |-> {} ]

InitNoBcast == /\ sent = {}
               /\ pc \in [ Corr -> {"V0"} ]
               /\ rcvd = [ i \in Corr |-> {} ]
        
 
Next ==  Step(0) \/ Step(1) \/ Step(2) \/ Step(3)

Spec == Init /\ [][Next]_vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

Fairness ==
    WF_vars(
        \E i \in Corr: Receive(i) /\ (UponV1(i) \/ UponAccept(i))
        )

TypeOK == /\ sent \subseteq P \times M
          /\ pc \in [ Corr -> {"V0", "V1", "SE", "AC"} ]
          /\ rcvd \in [ Corr -> SUBSET (P \times M) ]
          
Unforg == (\A self \in Corr: (pc[self] /= "AC")) 

UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] = "AC")
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\E i \in Corr: pc[i] = "AC")
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

FairCorr ==
    Fairness => CorrLtl

=============================================================================
\* Modification History
\* Last modified Fri Jun 19 00:14:34 CEST 2015 by igor
\* Created Thu Mar 12 00:46:19 CET 2015 by igor

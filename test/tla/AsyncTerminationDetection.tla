---------------------- MODULE AsyncTerminationDetection ---------------------
(***************************************************************************)
(* An abstract specification of the termination detection problem in a     *)
(* ring with asynchronous communication.                                   *)
(***************************************************************************)
EXTENDS Naturals
CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES 
  active,               \* activation status of nodes
  pending,              \* number of messages pending at a node
  terminationDetected   \* has termination been detected?

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending \in [Node -> Nat]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

(***************************************************************************)
(* Initial condition: the nodes can be active or inactive, no pending      *)
(* messages. Termination may (but need not) be detected immediately if all *)
(* nodes are inactive.                                                     *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending = [n \in Node |-> 0]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==  \* node i terminates
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ pending' = pending
     (* possibly (but not necessarily) detect termination if all nodes are inactive *)
  /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(i,j) ==  \* node i sends a message to node j
  /\ active[i]
  /\ pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, terminationDetected>>

Wakeup(i) == \* node i receives a pending message
  /\ pending[i] > 0
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED <<active, pending>>

Next ==
  \/ \E i \in Node : Wakeup(i) \/ Terminate(i)
  \/ \E i,j \in Node : SendMsg(i,j)
  \/ DetectTermination

vars == <<active, pending, terminationDetected>>
Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(DetectTermination)
           \* reasonable but not necessary for detecting termination
           \* /\ \A i \in Node : WF_vars(Wakeup(i))

(***************************************************************************)
(* Restrict TLC model checking to a finite fragment of the state space.    *)
(***************************************************************************)
StateConstraint == \A n \in Node : pending[n] <= 3

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
Stable == [](terminationDetected => []terminated)

Live == terminated ~> terminationDetected

=============================================================================
\* Modification History
\* Last modified Wed Jun 02 14:21:31 PDT 2021 by markus
\* Last modified Thu Jan 21 17:38:07 CET 2021 by merz
\* Created Sun Jan 10 15:19:20 CET 2021 by merz

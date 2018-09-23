------------ MODULE Bakery ----------------------------
(***************************************************************************)
(* The bakery algorithm originally appeared in:                            *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* The code for the algorithm given in that paper is :                     *)
(*                                                                      `. *)
(*   begin integer j;                                                      *)
(*   L1: choosing [i] := 1 ;                                               *)
(*       number[i] := 1 + maximum (number[1],..., number[N]);              *)
(*       choosing[i] := 0;                                                 *)
(*       for j = 1 step l until N do                                       *)
(*          begin                                                          *)
(*            L2: if choosing[j] /= 0 then goto L2;                        *)
(*            L3: if number[j] /= 0 and (number [j], j) < (number[i],i)    *)
(*                  then goto L3;                                          *)
(*          end;                                                           *)
(*       critical section;                                                 *)
(*       number[i] := O;                                                   *)
(*       noncritical section;                                              *)
(*       goto L1 ;                                                         *)
(*   end                                                               .'  *)
(*                                                                         *)
(* This PlusCal version of the Atomic Bakery algorithm is one in which     *)
(* variables whose initial values are not used are initialized to          *)
(* particular type-correct values.  If the variables were left             *)
(* uninitialized, the PlusCal translation would initialize them to a       *)
(* particular unspecified value.  This would complicate the proof because  *)
(* it would make the type-correctness invariant more complicated, but it   *)
(* would be efficient to model check.  We could write a version that is    *)
(* more elegant and easy to prove, but less efficient to model check, by   *)
(* initializing the variables to arbitrarily chosen type-correct values.   *)
(***************************************************************************)
EXTENDS Naturals

(*, TLAPS*)

(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)
\*CONSTANT N
\*ASSUME N \in Nat
MyNat == 0..7
N == 3
EmptyIntSet == {1} \ {1} \* THIS IS THE ANNOYING HACK
(***************************************************************************)
(* We define Procs to be the set {1, 2, ...  , N} of processes.            *)
(***************************************************************************)
Procs == 1..N 

(***************************************************************************)
(* \prec is defined to be the lexicographical less-than relation on pairs  *)
(* of numbers.                                                             *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(***       this is a comment containing the PlusCal code *

--algorithm Bakery 
{ variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1 ;
    { ncs:- while (TRUE) 
            { e1:   either { flag[self] := ~ flag[self] ;
                             goto e1 }
                    or     { flag[self] := TRUE;
                             unchecked := Procs \ {self} ;
                             max := 0
                           } ;     
              e2:   while (unchecked # {}) 
                      { with (i \in unchecked) 
                          { unchecked := unchecked \ {i};
                            if (num[i] > max) { max := num[i] }
                          }
                      };
              e3:   either { with (k \in MyNat) { num[self] := k } ;
                             goto e3 }
                    or     { with (i \in {j \in MyNat : j > max}) 
                               { num[self] := i }
                           } ;
              e4:   either { flag[self] := ~ flag[self] ;
                             goto e4 }
                    or     { flag[self] := FALSE;
                             unchecked := Procs \ {self} 
                           } ;
              w1:   while (unchecked # {}) 
                      {     with (i \in unchecked) { nxt := i };
                            await ~ flag[nxt];
                        w2: await \/ num[nxt] = 0
                                  \/ <<num[self], self>> \prec <<num[nxt], nxt>> ;
                            unchecked := unchecked \ {nxt};
                      } ;
              cs:   skip ;  \* the critical section;
              exit: either { with (k \in MyNat) { num[self] := k } ;
                             goto exit }
                    or     { num[self] := 0 } 
            }
    }
}

***     this ends the comment containg the pluscal code      **********)

\* BEGIN TRANSLATION  (this begins the translation of the PlusCal code)
VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> EmptyIntSet]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED <<unchecked, max>>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ max' = [max EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, nxt >>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # EmptyIntSet
                  THEN /\ \E i \in unchecked[self]:
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in MyNat:
                       num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ \E i \in {j \in MyNat : j > max[self]}:
                       num' = [num EXCEPT ![self] = i]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << flag, unchecked, max, nxt >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # EmptyIntSet
                  THEN /\ \E i \in unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ nxt' = nxt
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in MyNat:
                         num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION   (this ends the translation of the PlusCal code)

(***************************************************************************)
(* MutualExclusion asserts that two distinct processes are in their        *)
(* critical sections.                                                      *)
(***************************************************************************)
MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Inductive Invariant                                                 *)
(*                                                                         *)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)
TypeOK == /\ num \in [Procs -> MyNat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> MyNat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]             

(***************************************************************************)
(* Before(i, j) is a condition that implies that num[i] > 0 and, if j is   *)
(* trying to enter its critical section and i does not change num[i], then *)
(* j either has or will choose a value of num[j] for which                 *)
(*                                                                         *)
(*     <<num[i],i>> \prec <<num[j],j>>                                     *)
(*                                                                         *)
(* is true.                                                                *)
(***************************************************************************)
Before(i,j) == /\ num[i] > 0
               /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                  \/ /\ pc[j] = "e2"
                     /\ \/ i \in unchecked[j]
                        \/ max[j] >= num[i]
                  \/ /\ pc[j] = "e3"
                     /\ max[j] >= num[i]
                  \/ /\ pc[j] \in {"e4", "w1", "w2"}
                     /\ <<num[i],i>> \prec <<num[j],j>>
                     /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])


(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)  
Inv == (*/\ TypeOK *)
       /\ \A i \in Procs : 
             /\ \* This conjunct not needed for mutual exclusion, but needed
                \* to prove liveness
                (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)    
             /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0) \* remove test #1, delete w1 from set  test #9
             /\ (pc[i] \in {"e2", "e3"}) => flag[i]                     \* remove test #2
             /\ \* This conjunct not needed to prove mutual exclusion.  It's
                \* needed to prove liveness, but could be removed if the \prec
                \* in the wait condition were changed to \preceq.
                (pc[i] = "w2") => (nxt[i] # i)
             /\ \* This conjunct can be simplified to
                \*   pc[i] \in {"w1", "w2"} => i \notin unchecked[i]
                pc[i] \in {"e2", "w1", "w2"} => i \notin unchecked[i]  \* remove test #3, delete w2 from set test #10
             /\ (pc[i] \in {"w1", "w2"}) =>                             \* remove test #4
                   \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
             /\ /\ (pc[i] = "w2")
                /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]]) \* remove test #5 remove last /\  test #8
                   \/ pc[nxt[i]] = "e3"
                => max[nxt[i]] (* > *) >= num[i]                                  \* replace >= by >  test #7
             /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)      \* remove test #6

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of Mutual Exclusion                                               *)
(*                                                                         *)
(* This is a standard invariance proof, where <1>2 asserts that any step   *)
(* of the algorithm (including a stuttering step) starting in a state in   *)
(* which Inv is true leaves Inv true.  Step <1>4 follows easily from       *)
(* <1>1-<1>3 by simple temporal reasoning, but TLAPS does not yet do any   *)
(* temporal reasoning.                                                     *)
(***************************************************************************)
(*
THEOREM Spec => []MutualExclusion
<1> USE N \in MyNat DEFS Procs, Inv, TypeOK, Before, \prec, ProcSet 
<1>1. Init => Inv
  BY SMT DEF Init
<1>2. Inv /\ [Next]_vars => Inv'
  BY Z3 DEF Next,  ncs, p, e1, e2, e3, e4, w1, w2, cs, exit, vars
<1>3. Inv => MutualExclusion
  BY SMT DEF MutualExclusion
<1> HIDE DEF Inv
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
------------------------------------------------------------------------------ 
*)
Trying(i) == pc[i] = "e1"
InCS(i)   == pc[i] = "cs"
DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))
StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)
-----------------------------------------------------------------------------
=================
II == \A i \in Procs : 
        /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)             \* not needed
        /\ (pc[i] = "w2") => (nxt[i] # i)                            \* not found Test 6 (66734 states found)
        /\ pc[i] \in {"e2", "w1", "w2"} => i \notin unchecked[i]       \* not found Test 6 (7638 states found)
        /\ (pc[i] \in {"w1", "w2"}) =>                                 \* not found Test 3 (41148 states found)
              \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
        /\ /\ (pc[i] = "w2")                                           \* not found Test 2 (722052 states found)
           /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
              \/ pc[nxt[i]] = "e3"
           => max[nxt[i]] >= num[i]
        /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)       \* found Test 2 (2 steps, 427366 states found)
             
IInit == /\ num = <<0,1>> \* \in [Procs -> MyNat]
         /\ flag \in [Procs -> BOOLEAN ]
         /\ unchecked \in [Procs -> SUBSET Procs]
         /\ max \in [Procs ->  {0}] \* MyNat]
         /\ nxt \in [Procs ->  {1}]  \* Procs]
         /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs"}] 
         /\ II

(* /\ num \in [Procs -> MyNat]
         /\ flag \in [Procs -> BOOLEAN]
         /\ unchecked \in [Procs -> SUBSET Procs]
         /\ max \in [Procs ->  MyNat]
         /\ nxt \in [Procs ->  Procs]
         /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs"}] 
         /\ II  
*)

ISpec == IInit /\ [][Next]_vars
             
=============================================================================
\* Modification History
\* Last modified Thu Sep 20 18:13:47 PDT 2018 by markus
\* Last modified Thu Sep 20 10:16:53 PDT 2018 by markus
\* Last modified Thu Sep 20 05:45:00 PDT 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport

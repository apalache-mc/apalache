--------------------------- MODULE Bug2750 ---------------------------
(***************************************************************************)
(* Original problem and spec by Michel Charpentier                         *)
(* http://www.cs.unh.edu/~charpov/programming-tlabuffer.html               *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS 
    \* @type: Set(PROC);
    Producers,   (* the (nonempty) set of producers                       *)
    \* @type: Set(PROC);
    Consumers,   (* the (nonempty) set of consumers                       *)
    \* @type: Int;
    BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)

-----------------------------------------------------------------------------

VARIABLES 
    \* @type: Seq(PROC);
    buffer, 
    \* @type: Set(PROC);
    waitP, 
    \* @type: Set(PROC);
    waitC

(* define statement *)
isfull(b) == Len(b) = BufCapacity
isempty(b) == Len(b) = 0

\* @type: << Seq(PROC), Set(PROC), Set(PROC) >>;
vars == << buffer, waitP, waitC >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ buffer = << >>
        /\ waitP = {}
        /\ waitC = {}

p(self) == /\ (self \notin waitP)
           /\ IF isfull(buffer)
                 THEN /\ IF self \in Producers
                            THEN /\ waitP' = (waitP \union {self})
                                 /\ waitC' = waitC
                            ELSE /\ waitC' = (waitC \union {self})
                                 /\ waitP' = waitP
                      /\ UNCHANGED buffer
                 ELSE /\ buffer' = Append(buffer, self)
                      /\ IF waitC # {}
                            THEN /\ \E t \in waitC:
                                      waitC' = waitC \ {t}
                            ELSE /\ TRUE
                                 /\ waitC' = waitC
                      /\ waitP' = waitP

c(self) == /\ (self \notin waitC)
           /\ IF isempty(buffer)
                 THEN /\ IF self \in Producers
                            THEN /\ waitP' = (waitP \union {self})
                                 /\ waitC' = waitC
                            ELSE /\ waitC' = (waitC \union {self})
                                 /\ waitP' = waitP
                      /\ UNCHANGED buffer
                 ELSE /\ buffer' = Tail(buffer)
                      /\ IF waitP # {}
                            THEN /\ \E t \in waitP:
                                      waitP' = waitP \ {t}
                            ELSE /\ TRUE
                                 /\ waitP' = waitP
                      /\ waitC' = waitC

Next == (\E self \in Producers: p(self))
           \/ (\E self \in Consumers: c(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Inv == ~(waitP = Producers /\ waitC = Consumers)

=============================================================================
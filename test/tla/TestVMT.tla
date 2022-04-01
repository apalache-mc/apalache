-------------------------- MODULE TestVMT -----------------------------
(***********************************************************************)
(* Specification of an allocator managing a set of resources:          *)
(* - Clients can request sets of resources whenever all their previous *)
(*   requests have been satisfied.                                     *)
(* - Requests can be partly fulfilled, and resources can be returned   *)
(*   even before the full request has been satisfied. However, clients *)
(*   only have an obligation to return resources after they have       *)
(*   obtained all resources they requested.                            *)
(*                                                                     *)
(* This version of the specification is written in the fragment of     *)
(* TLA+ that corresponds to uninterpreted first-order logic.           *)
(***********************************************************************)
CONSTANTS
  \* @type: Set(CLIENT);
  Client,     \* set of all clients
  \* @type: Set(RESOURCE);
  Resource    \* set of all resources

\* ASSUME
\*  IsFiniteSet(Resource)

VARIABLES
  \* @typeAlias: CR_PRED = <<CLIENT, RESOURCE>> -> Bool;
  \* @type: CR_PRED;
  unsat,       \* set of all outstanding requests per process
  \* @type: CR_PRED;
  alloc        \* set of resources allocated to given process

(*
TypeInvariant ==
  /\ unsat \in [Client -> SUBSET Resource]
  /\ alloc \in [Client -> SUBSET Resource]
*)
-------------------------------------------------------------------------

(* Resource are available iff they have not been allocated. *)
available(r) == ~ \E c \in Client : alloc[c, r]

(* Initially, no resources have been requested or allocated. *)
Init ==
  /\ unsat = [c \in Client, r \in Resource |-> FALSE]
  /\ alloc = [c \in Client, r \in Resource |-> FALSE]

(**********************************************************************)
(* A client c may request a set of resources provided that all of its *)
(* previous requests have been satisfied and that it doesn't hold any *)
(* resources.                                                         *)
(**********************************************************************)
Request(c,S) ==
  /\ \A r \in Resource : ~ unsat[c, r] /\ ~ alloc[c, r]
  /\ unsat' = [ cl \in Client, r \in Resource |->
    IF cl = c
    THEN S[r]
    ELSE unsat[cl,r]
   ]
  /\ UNCHANGED alloc

(*******************************************************************)
(* Allocation of a set of available resources to a client that     *)
(* requested them (the entire request does not have to be filled). *)
(*******************************************************************)
Allocate(c,S) ==
  /\ \A r \in Resource : S[r] => available(r) /\ unsat[c, r]
  /\ alloc' = 
    [ cl \in Client, r \in Resource |->
      IF cl = c
      THEN alloc[c,r] \/ S[r]
      ELSE alloc[cl, r]
     ]
  /\ unsat' = 
    [
      cl \in Client, r \in Resource |->
        IF cl = c
        THEN unsat[c,r] /\ ~S[r]
        ELSE unsat[cl,r]
    ]

(*******************************************************************)
(* Client c returns a set of resources that it holds. It may do so *)
(* even before its full request has been honored.                  *)
(*******************************************************************)
Return(c,S) ==
  /\ \A r \in Resource : S[r] => alloc[c,r]
  /\ alloc' = 
    [ cl \in Client, r \in Resource |->
      IF cl = c
      THEN alloc[c,r] /\ ~S[r]
      ELSE alloc[cl, r]
     ]
  /\ UNCHANGED unsat

(* The next-state relation. *)
Next ==
  \E c \in Client, S \in [Resource -> BOOLEAN] :
     Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

\* @type: <<CR_PRED, CR_PRED>>;
vars == <<unsat,alloc>>

Inv == TRUE

-------------------------------------------------------------------------

(* The complete high-level specification. *)
SimpleAllocator == Init /\ [][Next]_vars

-------------------------------------------------------------------------

Mutex == \A c1,c2 \in Client : \A r \in Resource :
            alloc[c1,r] /\ alloc[c2,r] => c1 = c2

=========================================================================

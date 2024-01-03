---- MODULE Bug1682 ----

EXTENDS Integers, Variants

(*
 @typeAlias: MESSAGE =
      RequestVote({ term: Int, from: Str })
    | Vote({ from: Str, to: Str, term: Int })
    | AppendEntries({ term: Int, from: Str }) ;
 *)
dummy_alias == TRUE

\* In contrast to untyped TLA+, we introduce three constructors for the variants.

\* @type: (Str, Int) => MESSAGE;
MkRequestVote(from, term) ==
    Variant("RequestVote", [ term |-> term, from |-> from ])

\* @type: (Str, Str, Int) => MESSAGE;
MkVote(from, to, term) ==
    Variant("Vote", [ term |-> term, to |-> to, from |-> from ])

\* @type: (Str, Int) => MESSAGE;
MkAppendEntries(from, term) ==
    Variant("AppendEntries", [ term |-> term, from |-> from ])

Server == {"s1", "s2", "s3"}
Quorum == {{"s1","s2"},{"s2","s3"},{"s1","s3"}}
Term == 0..2

Message ==  
    { MkRequestVote(from, term): from \in Server, term \in Term }
        \union
    { MkVote(from, to, term): from \in Server, to \in Server, term \in Term }
        \union
    { MkAppendEntries(from, term): from \in Server, term \in Term }

VARIABLE 
    \* @type: Str -> Int;
    currentTerm,
     \* @type: Set(MESSAGE);
    messages

vars == <<currentTerm, messages>>

Init ==
    /\ currentTerm = [s \in Server |-> 0]
    /\ messages = {}

BecomeCandidate(s) ==
    /\ currentTerm[s]<2
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ messages' = messages \union { MkRequestVote(s, currentTerm[s] + 1) }

Vote(s) ==
    /\ \E m \in VariantFilter("RequestVote", messages):
        /\ m.term > currentTerm[s]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
        /\ messages' = messages \union { MkVote(s, m.from, m.term) }

BecomeLeader(s) ==
    /\ \E Q \in Quorum:
        \A s1 \in Q: 
            \E m \in VariantFilter("Vote", messages):
                /\ m.term = currentTerm[s]
                /\ m.from = s1
                /\ m.to = s
    /\ messages' = messages \union { MkAppendEntries(s, currentTerm[s]) }
    /\ UNCHANGED <<currentTerm>>

Noop ==
    /\ UNCHANGED <<currentTerm,messages>>    

Next ==
    \/ \E s \in Server:
        \/ BecomeCandidate(s)
        \/ Vote(s)
        \/ BecomeLeader(s)
    \/ Noop

Spec == Init /\ [][Next]_vars

Safety ==
    \A t \in Term: \A m1, m2 \in VariantFilter("AppendEntries", messages):
        /\ m1.term = m2.term 
        => m1.from = m2.from 

TypeOK ==
    /\ currentTerm \in [Server -> Term]
    /\ messages \in SUBSET Message

\* True if server s is a leader in term t
IsLeader(s,t) ==
    \E Q \in Quorum:
        \A s1 \in Q: 
            \E m \in VariantFilter("Vote", messages):
                /\ m.term = t
                /\ m.from = s1
                /\ m.to = s


Inv == 
    /\ TypeOK
    /\ \A s \in Server:
        LET \* using a row variable in the record type:
            \* @type: { from: Str, term: Int, a } => Bool;
            IsOk(m) == m.from = s => currentTerm[s] >= m.term
        IN
        /\ \A m \in VariantFilter("Vote", messages): IsOk(m)
        /\ \A m \in VariantFilter("AppendEntries", messages): IsOk(m)
        /\ \A m \in VariantFilter("RequestVote", messages): IsOk(m)
    /\ \A m1, m2 \in VariantFilter("Vote", messages):
       \A s \in Server: 
       /\ m1.from = s 
       /\ m2.from = s 
       /\ m1.term = m2.term 
       => m1.to = m2.to
    /\ \A t \in Term: \A s1, s2 \in Server:
       /\ IsLeader(s1,t) 
       /\ IsLeader(s2,t) 
       => s1=s2

=================

---- MODULE Bug1682 ----

EXTENDS Integers

Server == {"s1", "s2", "s3"}
Quorum == {{"s1","s2"},{"s2","s3"},{"s1","s3"}}
Term == 0..2

Message ==  
    [type : {"RequestVote"}, term : Term, from: Server]
    \cup [type : {"Vote"}, from : Server, to: Server, term : Term]
    \cup [type : {"AppendEntries"}, term : Term, from: Server]

VARIABLE 
    \* @type: Str -> Int;
    currentTerm,
     \* @type: Set([type: Str, term: Int, from: Str, to:Str]);
    messages

vars == <<currentTerm, messages>>

Init ==
    /\ currentTerm = [s \in Server |-> 0]
    /\ messages = {}

BecomeCandidate(s) ==
    /\ currentTerm[s]<2
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ messages' = messages \union {[type |-> "RequestVote", term |-> currentTerm[s]+1, from |-> s]}

Vote(s) ==
    /\ \E m \in messages:
        /\ m.type = "RequestVote"
        /\ m.term > currentTerm[s]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
        /\ messages' = messages \union {[type |-> "Vote", 
                                            term |-> m.term, from |-> s, to |-> m.from]}

BecomeLeader(s) ==
    /\ \E Q \in Quorum:
        \A s1 \in Q: 
            \E m \in messages: 
                /\ m.type = "Vote"
                /\ m.term = currentTerm[s]
                /\ m.from = s1
                /\ m.to = s
    /\ messages' = messages \union {[type |-> "AppendEntries", 
                                        term |-> currentTerm[s], from |-> s]}
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
    \A t \in Term: \A m1,m2 \in messages: 
        /\ m1.type = "AppendEntries" 
        /\ m2.type = "AppendEntries" 
        /\ m1.term = m2.term 
        => m1.from = m2.from 

TypeOK ==
    /\ currentTerm \in [Server -> Term]
    /\ messages \in SUBSET Message

\* True if server s is a leader in term t
IsLeader(s,t) ==
    \E Q \in Quorum:
        \A s1 \in Q: 
            \E m \in messages: 
                /\ m.type = "Vote"
                /\ m.term = t
                /\ m.from = s1
                /\ m.to = s


Inv == 
    /\ TypeOK
    /\ \A s \in Server, m \in messages: 
        m.from = s => currentTerm[s] \geq m.term
    /\ \A m1,m2 \in messages: \A s \in Server: 
       /\ m1.type = "Vote" 
       /\ m2.type = "Vote" 
       /\ m1.from = s 
       /\ m2.from = s 
       /\ m1.term = m2.term 
       => m1.to = m2.to
    /\ \A t \in Term: \A s1,s2 \in Server:
       /\ IsLeader(s1,t) 
       /\ IsLeader(s2,t) 
       => s1=s2

=================
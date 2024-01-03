---- MODULE Consensus_epr ----
\* Spec used to test function operations, based on consensus-epr from
\* https://github.com/will62794/endive-artifact/tree/0ccc16dadcf16bed6ac72aa71bd6563d683c63d1
EXTENDS TLC, Naturals, FiniteSets, Sequences

Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

Quorum == {
    {"1_OF_N", "2_OF_N"},
    {"1_OF_N", "3_OF_N"},
    {"2_OF_N", "3_OF_N"}
}

Value == { "1_OF_V", "2_OF_V" }

VARIABLE
    \* @type: Set(<<N, N>>);
    vote_request_msg,
    \* @type: N -> Bool;
    voted,
    \* @type: Set(<<N, N>>);
    vote_msg,
    \* @type: N -> Set(N);
    votes,
    \* @type: N -> Bool;
    leader,
    \* @type: N -> Set(V);
    decided

SendRequestVote(src, dst) ==
    /\ vote_request_msg' = vote_request_msg \cup {<<src, dst>> }
    /\ UNCHANGED <<voted,vote_msg,votes,leader,decided>>

SendVote(src, dst) ==
    /\ ~voted[src]
    /\ <<dst,src>> \in vote_request_msg
    /\ vote_msg' = vote_msg \cup {<<src,dst>>}
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ \/ vote_request_msg' = vote_request_msg \cup {<<src,dst>>}
       \/ vote_request_msg' = vote_request_msg \ {<<src,dst>>}
    /\ UNCHANGED <<votes, leader, decided>>

RecvVote(n, sender) ==
    /\ <<sender,n>> \in vote_msg
    /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {sender}]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,leader,decided>>

BecomeLeader(n, Q) ==
    /\ Q \subseteq votes[n]
    /\ leader' = [leader EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,votes,decided>>

Decide(n, v) ==
    /\ leader[n]
    /\ decided[n] = {}
    /\ decided' = [decided EXCEPT ![n] = decided[n] \cup {v}]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,votes,leader>>

Init ==
    /\ vote_request_msg = {}
    /\ voted = [i \in Node |-> FALSE]
    /\ vote_msg = {}
    /\ votes = [i \in Node |-> {}]
    /\ leader = [i \in Node |-> FALSE]
    /\ decided = [i \in Node |-> {}]

Next ==
    \/ \E i,j \in Node : SendRequestVote(i,j)
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
    \/ \E i,j \in Node, v \in Value : Decide(i,v)

Safety ==
    \A n1,n2 \in Node, v1,v2 \in Value :
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)

====

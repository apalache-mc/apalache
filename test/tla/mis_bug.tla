-------------------------------- MODULE mis_bug --------------------------------
EXTENDS Integers, TLC

N == 3
N4 == 81
Nodes == 1..N

VARIABLES Nb, round, val, awake, rem_nbrs, status, msgs

Pred(n) == IF n > 1 THEN n - 1 ELSE N
Succ(n) == IF n < N THEN n + 1 ELSE 1

Init == /\ Nb = [ n \in Nodes |-> {Pred(n), Succ(n)} ]
        /\ round = 1
        /\ val \in [Nodes -> 1..N4]
        /\ awake = [n \in Nodes |-> TRUE]
        /\ rem_nbrs = Nb
        /\ status = [n \in Nodes |-> "unknown"]
        /\ msgs = [n \in Nodes |-> {}]
    
Senders(u) == {v \in Nodes: awake[v] /\ u \in rem_nbrs[v] }

SentValues(u) == { val'[w] : w \in Senders(u) }
    
IsWinner(u) == \A v \in msgs'[u]: TRUE \*val'[u] > v \* replace with TRUE to introduce a bug
    
Round1 ==
    /\ round = 1
    /\ val' \in [Nodes -> 1..N4] \* non-determinism, no randomness
    /\ msgs' = [u \in Nodes |-> SentValues(u)]
    /\ status' = [n \in Nodes |->
        IF awake[n] /\ IsWinner(n) THEN "winner" ELSE status[n]]
    /\ UNCHANGED <<rem_nbrs, awake>>

SentWinners(u) ==
    IF \E w \in Senders(u): awake[w] /\ status[w] = "winner"
    THEN {"winner"}
    ELSE {}

IsLoser(u) == "winner" \in msgs'[u]
    
Round2 ==
    /\ round = 2
    /\ msgs' = [u \in Nodes |-> SentWinners(u)]
    /\ status' = [n \in Nodes |->
        IF awake[n] /\ IsLoser(n) THEN "loser" ELSE status[n]]
    /\ UNCHANGED <<rem_nbrs, awake, val>>

SentLosers(u) ==
    {w \in Senders(u): awake[w] /\ status[w] = "loser"}
    
Round3 ==
    /\ round = 3 
    /\ msgs' = [u \in Nodes |-> SentLosers(u)]
    /\ awake' = [n \in Nodes |->
        IF status[n] \notin {"winner", "loser"} THEN TRUE ELSE FALSE]
    /\ rem_nbrs' = [u \in Nodes |-> rem_nbrs[u] \ msgs'[u]] 
    /\ UNCHANGED <<status, val>>

Next ==
    round' = 1 + (round % 3) /\ (Round1 \/ Round2 \/ Round3) /\ UNCHANGED <<Nb>>
    
IsIndependent ==
    \A u \in Nodes: \A v \in Nb[u]:
        (status[u] /= "winner" \/ status[v] /= "winner")

Terminated == \A n \in Nodes: awake[n] = FALSE

=============================================================================
\* Modification History
\* Last modified Thu Jul 19 21:28:53 BST 2018 by igor
\* Created Sun Jul 15 17:03:47 CEST 2018 by igor

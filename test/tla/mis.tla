-------------------------------- MODULE mis --------------------------------
EXTENDS Integers, TLC

N == 3
N4 == 81
Nodes == 1..N

a <: b == a \* type annotations

VARIABLES
    \* @type: Set(<<Int, Int>>);
    Nb,
    \* @type: Int;
    round,
    \* @type: Int -> Int;
    val,
    \* @type: Int -> Bool;
    awake,
    \* @type: Int -> Set(Int);
    rem_nbrs,
    \* @type: Int -> Str;
    status,
    \* @type: Int -> Set([type: Str, src: Int, val: Int]);
    msgs

Pred(n) == IF n > 1 THEN n - 1 ELSE N
Succ(n) == IF n < N THEN n + 1 ELSE 1

Init == \*/\ Nb = [ n \in Nodes |-> {Pred(n), Succ(n)} ]
        /\ Nb \in SUBSET(Nodes \X Nodes)
        /\ \A e \in Nb: <<e[2], e[1]>> \in Nb \* the graph is undirected
        /\ round = 1
        /\ val \in [Nodes -> 1..N4]
        /\ awake = [n \in Nodes |-> TRUE]
        /\ rem_nbrs = [ u \in Nodes |-> { v \in Nodes : <<u, v>> \in Nb}]
        /\ status = [n \in Nodes |-> "unknown"]
        /\ msgs = [n \in Nodes |->
            ({} <: {[type |-> STRING, src |-> Int, val |-> Int ]})]
    
Senders(u) == {v \in Nodes: awake[v] /\ u \in rem_nbrs[v] }

SentValues(u) == { [type |-> "val", src |-> w, val |-> val'[w]] : w \in Senders(u) }
    
IsWinner(u) ==
    \A m \in msgs'[u]:
        m.type = "val" => val'[u] > m.val \* replace with TRUE to introduce a bug
    
Round1 ==
    /\ round = 1
    /\ val' \in [Nodes -> 1..N4] \* non-determinism, no randomness
    /\ msgs' = [u \in Nodes |-> SentValues(u)]
    /\ status' = [n \in Nodes |->
        IF awake[n] /\ IsWinner(n) THEN "winner" ELSE status[n]]
    /\ UNCHANGED <<rem_nbrs, awake>>

SentWinners(u) ==
    IF \E w \in Senders(u): awake[w] /\ status[w] = "winner"
    THEN {[type |-> "winner", src |-> u]
            <: [type |-> STRING, src |-> Int, val |-> Int]}
    ELSE ({}
            <: {[type |-> STRING, src |-> Int, val |-> Int]})

IsLoser(u) == \E m \in msgs'[u]: m.type = "winner"
    
Round2 ==
    /\ round = 2
    /\ msgs' = [u \in Nodes |-> SentWinners(u)]
    /\ status' = [n \in Nodes |->
        IF awake[n] /\ IsLoser(n) THEN "loser" ELSE status[n]]
    /\ UNCHANGED <<rem_nbrs, awake, val>>

SentLosers(u) ==
    {([type |-> "loser", src |-> s]
        <: [type |-> STRING, src |-> Int, val |-> Int])
        : s \in {w \in Senders(u): awake[w] /\ status[w] = "loser"}}

ReceivedLosers(u) ==
    {mm.src : mm \in {m \in msgs'[u]: m.type = "loser"}}
    
Round3 ==
    /\ round = 3 
    /\ msgs' = [u \in Nodes |-> SentLosers(u)]
    /\ awake' = [n \in Nodes |->
        IF status[n] \notin {"winner", "loser"} THEN TRUE ELSE FALSE]
    /\ rem_nbrs' = [u \in Nodes |-> rem_nbrs[u] \ ReceivedLosers(u)] 
    /\ UNCHANGED <<status, val>>

Next ==
    round' = 1 + (round % 3) /\ (Round1 \/ Round2 \/ Round3) /\ UNCHANGED Nb
    
IsIndependent ==
    \A edge \in Nb:
        (status[edge[1]] /= "winner" \/ status[edge[2]] /= "winner")

Terminated == \A n \in Nodes: awake[n] = FALSE

=============================================================================
\* Modification History
\* Last modified Thu Jul 19 21:28:53 BST 2018 by igor
\* Created Sun Jul 15 17:03:47 CEST 2018 by igor

--------------------------------- MODULE pr ---------------------------------
(**
 Partial link reversal. See:
 
   E. M. Gafni and D. P. Bertsekas, Distributed algorithms for generating loop-free routes in
   networks with frequently changing topology, IEEE Trans. Commun., 29 (1981), pp. 11–18.
   
   We consider directed acyclic graphs that are not necessarily connected.
   The algorithm has an interesting safety property:
   the directed graph generated at each iteration is acyclic.

   Igor Konnov, 2018
 *)
EXTENDS Integers
 
\*CONSTANTS N, dest

N == 4
dest == 1

Nodes == 1..N
a <: b == a
EmptyIntSet == {} <: {Int}

VARIABLES out, in, to_rev

IsDag ==
  \E po \in [Nodes -> [Nodes -> BOOLEAN]]:  \* there is a partial order, that is,
    /\ \A u \in Nodes: po[u][u]                                 \* reflexive         
    /\ \A u, v, w \in Nodes: po[u][v] /\ po[v][w] => po[u][w]   \* transitive
    /\ \A u, v \in Nodes: po[u][v] /\ po[v][u] => u = v         \* antisymmetric
    /\ \A u \in Nodes: \A v \in out[u]: po[u][v]                \* embeds neighborhood

InitOut ==
    \* [ u \in Nodes |-> IF u = 1 THEN {2} ELSE EmptyIntSet ]
    [ u \in Nodes |->
        IF u = 2 THEN {3, 5} ELSE IF u \in { 3, 7} THEN {4}
        ELSE IF u = 5 THEN {6} ELSE IF u = 6 THEN {3, 7}
        ELSE EmptyIntSet \* u \in {1, 4}
    ]

Init ==
    /\ out = InitOut
    /\ in = [u \in Nodes |-> {v \in Nodes: u \in out[v]}]
    /\ to_rev = [n \in Nodes |-> EmptyIntSet (*{}*)]
    \*/\ out \in [Nodes -> SUBSET(Nodes)]
    \*/\ IsDag
    
    
Sinks == { n \in Nodes : out[n] = EmptyIntSet (*{}*) /\ n /= dest}

Reversed(Active) ==
    [ u \in Nodes |-> \* TODO: figure out, why it does not work with Active
        IF u \notin Active
        THEN EmptyIntSet
        ELSE IF in[u] /= to_rev[u] THEN in[u] \ to_rev[u] ELSE in[u] ]

UpdateOut(Active, rev) ==
    out' = [ u \in Nodes |->
        IF u \in Active
        THEN rev[u] \* active sink => turn all reversed in nodes into out
        ELSE out[u] \ { s \in Active : u \in rev[s] }
            \* another node => remove the nodes that active sinks reversed 
    ]

UpdateIn(Active, rev) ==
    in' = [ u \in Nodes |->
        IF u \in Active
        THEN in[u] \ rev[u] \* active sink => leave those nodes that are not reversed
        ELSE in[u] \cup { s \in Active : u \in rev[s] }
            \* another node => add the nodes from the sinks that reversed this edge
    ]
    
UpdateToRev(Active, rev) ==
    to_rev' = [ u \in Nodes |->
        IF u \in Active
        THEN EmptyIntSet (*{}*) \* empty the list of the links to reverse
        ELSE to_rev[u] \cup { s \in Active : u \in rev[s] }
            \* when a neighbor s of u makes a reversal, u adds
            \* the link between u and s to the list
    ]

Next ==
    \E Active \in SUBSET(Sinks):
        LET rev == Reversed(Active) IN
            /\ UpdateToRev(Active, rev) \* XXX
            /\ UpdateOut(Active, rev)
            /\ UpdateIn(Active, rev)

=============================================================================
\* Modification History
\* Last modified Sun Jul 15 17:03:49 CEST 2018 by igor
\* Created Fri Jul 06 17:35:52 CEST 2018 by igor

----------------------- MODULE PickPerf ---------------------------------------
VARIABLES
    \* @type: Set(Int);
    S,
    \* @type: Set(Int);
    T,
    \* @type: Set(Int);
    R,
    \* @type: Int;
    state

Init ==
    /\ S = { 1 }
    /\ T = { 4 }
    /\ R = S \union T
    /\ state = 0

Next ==
  /\\/ 1 \in S /\ S' = { 2 } \union S /\ UNCHANGED T
    \/ 2 \in S /\ S' = { 3 } \union S /\ UNCHANGED T
    \/ 3 \in S /\ S' = { 1 } \union S /\ UNCHANGED T
    \/ 4 \in T /\ T' = { 5 } \union T /\ UNCHANGED S
    \/ 5 \in T /\ T' = { 6 } \union T /\ UNCHANGED S
    \/ 6 \in T /\ T' = { 1 } \union T /\ UNCHANGED S
  /\ R' = S' \union T'
  /\\/ state = 0 /\ state' = 1
    \/ state = 0 /\ state' = 2
    \/ state = 1 /\ state' = 3
    \/ state = 2 /\ state' = 1
    \/ state = 2 /\ state' = 4
    \/ state = 1 /\ state' = 0
    \/ UNCHANGED state

Inv ==
    S /= T

===============================================================================

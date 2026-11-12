---- MODULE Bug3493 ----
EXTENDS Integers

VARIABLES
    \* @type: Set({ v: Int });
    reqs,
    \* @type: Int;
    ver,
    \* @type: Int;
    got

Init == reqs = {} /\ ver = 0 /\ got = -1

\* The version only changes while no request is pending.
Bump == reqs = {} /\ ver' = ver + 1 /\ got' = -1 /\ UNCHANGED reqs

Request == reqs' = reqs \union {[v |-> ver]} /\ UNCHANGED <<ver, got>>

Respond == reqs /= {} /\ \E r \in reqs: got' = r.v /\ UNCHANGED <<reqs, ver>>

Next == Bump \/ Request \/ Respond

\* Every request carries the current version, so every answer matches it.
Inv == got = -1 \/ got = ver
====

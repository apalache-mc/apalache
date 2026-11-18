---- MODULE Bug3493Tuple ----
EXTENDS Integers
VARIABLES
    \* @type: Set(<<Int, Int>>);
    reqs,
    \* @type: Int;
    ver,
    \* @type: Int;
    got
Init == reqs = {} /\ ver = 0 /\ got = -1
Bump == reqs = {} /\ ver' = ver + 1 /\ got' = -1 /\ UNCHANGED reqs
Request == reqs' = reqs \union {<<ver, 0>>} /\ UNCHANGED <<ver, got>>
Respond == reqs /= {} /\ \E r \in reqs: got' = r[1] /\ UNCHANGED <<reqs, ver>>
Next == Bump \/ Request \/ Respond
Inv == got = -1 \/ got = ver
====

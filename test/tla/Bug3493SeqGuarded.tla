---- MODULE Bug3493SeqGuarded ----
EXTENDS Integers, Sequences
VARIABLES
    \* @type: Set(Seq(Int));
    reqs,
    \* @type: Int;
    ver,
    \* @type: Int;
    got
Init == reqs = {} /\ ver = 0 /\ got = -1
Bump == reqs = {} /\ ver' = ver + 1 /\ got' = -1 /\ UNCHANGED reqs
Request == reqs' = reqs \union {<<ver>>} /\ UNCHANGED <<ver, got>>
Respond == reqs /= {} /\ \E r \in reqs: Len(r) = 1 /\ got' = r[1] /\ UNCHANGED <<reqs, ver>>
Next == Bump \/ Request \/ Respond
Inv == got = -1 \/ got = ver
====

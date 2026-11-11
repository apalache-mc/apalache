---- MODULE Bug3493SeqPick ----
EXTENDS Integers, Sequences
VARIABLES
    \* @type: Set(Seq(Int));
    seqs,
    \* @type: Seq(Int);
    got
Init == seqs = {<<1>>, <<2, 3>>} /\ got = <<>>
Next == \E s \in seqs: got' = s /\ UNCHANGED seqs
Inv == Len(got) <= 2
====

---------- MODULE SelectSeqTests ----------

EXTENDS Integers, Sequences

VARIABLE
    \* @type: Int;
    x

AllPass(p) == TRUE
AllFail(p) == FALSE
AllEven(p) == p % 2 = 0
AllGt1(p) == p > 1

\* @type: Seq(Int);
seq == <<1,2,3>>

Init == x = 0

Next == x' = 1

Inv1 == SelectSeq(seq, AllPass) = seq
Inv2 == SelectSeq(seq, AllFail) = <<>>
Inv3 == SelectSeq(seq, AllEven) = <<2>>
Inv4 == SelectSeq(seq, AllGt1) = <<2,3>>

Inv == Inv1 /\ Inv2 /\ Inv3 /\ Inv4

====================
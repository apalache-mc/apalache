--------------------- MODULE Select575 ---------------------------------
EXTENDS Sequences, Integers

VARIABLE myseq

Select(seq, test(_)) ==
  LET RECURSIVE select(_, _)
      select(t(_), s) ==
        CASE s = <<>> -> <<>>
          [] t(Head(s)) -> Head(s)
          [] OTHER -> select(t, Tail(s))
  IN select(test, seq)

Init ==
  myseq = << 1, 2, 3 >>

Next ==
  LET IsEven(i) == i % 2 = 0 IN
  myseq' = Select(myseq, IsEven)
=========================================================================

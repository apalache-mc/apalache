----------------- MODULE SelectSeqWorkaround ---------------------------------
(*
 * The current version of Apalache does not support Sequences!SelectSeq.
 * We also do not know, how to implement it solely in the model checker,
 * as it the only standard operator that requires a higher order operator
 * as its argument. Apalache inlines all operator definitions, which cannot
 * be done for SelectSeq.
 *
 * Luckily, the definition of SelectSeq by Leslie Lamport almost fits our
 * purposes. Here, we adapt it a bit to, in order to avoid type annotations.
 *
 * We do not replace automatically Sequences!SelectSeq with this implementation.
 * It is a bit too complex. If a type error occurs in this operator, then
 * the user should see it.
 *
 * Igor Konnov, Oct 2020
 *)
EXTENDS Integers, Sequences

(****************************************************************************)
(* The rest of the code is testing this implementation                      *)  
(****************************************************************************)

VARIABLES seq1, seq2, seq3

a <: b == a

IsOdd(i) == i % 2 = 1

GreaterThanTen(i) == i > 10

Init ==
    (**
     * This implementation is similar to the canonical implementation of SelectSeq.
     * However, it avoids the operators that Apalache does not support well.
     *)
    LET MySelectSeq(seq, Test(_)) ==
      LET F[i \in {0} \union DOMAIN seq] ==
        IF i = 0
        THEN SubSeq(seq, 1, 0) \* this operation preserves the type
        ELSE
          LET prev == F[i - 1] IN
          LET ith == seq[i] IN
          IF Test(ith)
          THEN Append(prev, ith)
          ELSE prev
      IN
      F[Len(seq)]
    IN
    /\ seq1 = (<<0, 2, 1, 4, 7>> <: Seq(Int))
    /\ seq2 = MySelectSeq(seq1, IsOdd)
    /\ seq3 = MySelectSeq(seq1, GreaterThanTen)

Next == UNCHANGED <<seq1, seq2, seq3>>

Inv2 == seq2 = <<1, 7>> <: Seq(Int)

Inv3 == Len(seq3) = 0

==============================================================================

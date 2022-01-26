---- MODULE TlcSpec1 -----
(*
 Tests for type checking TLC operators
 *)

EXTENDS TLC

\* TLC
TlcPrint == Print("hello", 3)
TlcPrintT == PrintT("world")
TlcAssert == Assert(4 /= 3, "no way")
TlcJavaTime == JavaTime
\* #type: () => Int;
TlcGet == TLCGet(3)
TlcSet == TLCSet(3, "a")

TlcSmiley == 1 :> "a"
TlcAtAt == (1 :> "a")  @@ (2 :> "b")

TlcPermutations == Permutations({1, 2})
\* #type: (Seq(Int), ((Int, Int) => Bool)) => (Int -> Int);
TlcSortSeq(seq, F(_, _)) == SortSeq(seq, F)
TlcRandomElement == RandomElement({1, 2})
\* #type: () => Int;
TlcAny == Any
TlcToString == ToString(12)
TlcEval == TLCEval(10)
===============================================================================
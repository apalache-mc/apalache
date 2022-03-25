------------------------ MODULE TestFolds -------------------------------------
(**
 * A test for the community module Folds.
 * Since our implementation calls __NotSupportedByModelChecker,
 * it is only useful to test it with a type checker.
 *)

EXTENDS Folds

Init == TRUE

Next == TRUE

Test1 ==
    LET \* @type: Seq(Set(Str));
        seq == <<{"a"}, {"b"}, {"c"}>>
    IN
    LET F(i) == seq[i] IN
    LET unite(S, T) == S \union T IN
    LET choose(S) == CHOOSE x \in S: TRUE IN
    MapThenFoldSet(unite, {}, F, choose, { 2, 3 }) = { "b", "c" }

AllTests ==
    Test1

===============================================================================

------------------- MODULE OptionTests -----------------------
EXTENDS Naturals, Apalache, Option

\* @type: Set(Int) => Some(Int) | None(UNIT);
MaxSet(s) ==
  LET max(oa, b) ==
    IF OptionGetOrElse(oa, b) > b
    THEN oa
    ELSE Some(b)
  IN
  ApaFoldSet(max, None, s)

TestMap ==
    /\ OptionMap(LAMBDA x: x + 1, Some(2)) = Some(3)
    /\ OptionMap(LAMBDA x: x + 1, None) = None
    /\ OptionMap(LAMBDA s: s \union {"B"}, Some({"A"})) = Some({"A", "B"})

TestMaxSet ==
    /\ MaxSet({1,3,4,2}) = Some(4)
    /\ MaxSet({}) = None

TestOptionCase ==
    /\ LET
        \* @type: Int => Int;
        caseSome(x) == x + 1
      IN LET
        \* @type: UNIT => Int;
        caseNone(u) == 0
      IN
      OptionCase(Some(3), caseSome, caseNone) = 4
    /\ LET
        \* @type: Int => Str;
        caseSome(x) == "Some Number"
      IN LET
        \* @type: UNIT => Str;
        caseNone(u) == "None"
      IN
      OptionCase(None, caseSome, caseNone) = "None"

TestOptionToSeq ==
    LET \* @type: Seq(Int);
      empty == <<>>
    IN
    /\ OptionToSeq(None) = empty
    /\ OptionToSeq(Some(1)) = <<1>>

TestOptionToSet ==
    LET \* @type: Set(Int);
      empty == {}
    IN
    /\ OptionToSet(None) = empty
    /\ OptionToSet(Some(1)) = {1}

TestOptionFlatMap ==
    LET incr(n) == Some(n + 1) IN
    LET fail(n) == None IN
    LET q == OptionFlatMap(incr, Some(1)) IN
    LET r == OptionFlatMap(incr, q) IN
    LET s == OptionFlatMap(fail, r) IN
    /\ r = Some(3)
    /\ s = None

TestOptionGuess ==
    LET
      \* @type: Set(Int);
      empty == {}
    IN
    /\ OptionGuess(empty) = None
    /\ LET choices == {1,2,3,4} IN
      LET choice == OptionGuess(choices) IN
      VariantGetUnsafe("Some", choice) \in choices

TestOptionFunApp ==
    LET f == [x \in 1..3 |-> x + 1] IN
    /\ OptionFunApp(f, Some(1)) = Some(2)
    /\ OptionFunApp(f, None) = None

TestOptionPartialFun ==
    LET def == 1..3 IN
    LET undef == 4..10 IN
    LET f == [x \in def |-> x + 1] IN
    LET pf == OptionPartialFun(f, undef) IN
    /\ \A n \in def: pf[n] = Some(n + 1)
    /\ \A n \in undef: pf[n] = None

Next == TRUE
Init ==
    /\ TestMap
    /\ TestMaxSet
    /\ TestOptionCase
    /\ TestOptionFlatMap
    /\ TestOptionToSeq
    /\ TestOptionToSet
    /\ TestOptionGuess
    /\ TestOptionFunApp
    /\ TestOptionPartialFun

============================================================

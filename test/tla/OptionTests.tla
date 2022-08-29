------------------- MODULE OptionTests -----------------------
EXTENDS Naturals, Apalache, Option

\* @type: Set(a) => $option;
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

TestFlatMap ==
    LET q == FlatMap(LAMBDA x: Some(x + 1), Some(1)) IN
    LET r == FlatMap(LAMBDA x: Some(x + 1), q) IN
    LET s == FlatMap(LAMBDA x: None, r) IN
    /\ r = Some(3)
    /\ s = None

Next == TRUE
Init ==
    /\ TestMap
    /\ TestMaxSet
    /\ TestOptionCase
    /\ TestOptionToSeq
    /\ TestOptionToSet
    /\ TestFlatMap

============================================================

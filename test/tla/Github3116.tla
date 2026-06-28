------------------------------- MODULE Github3116 -------------------------------
\* Regression test for https://github.com/apalache-mc/apalache/issues/3116:
\* OptionCase with an un-annotated caseNone (returning None) used to crash the
\* model checker with a confusing "Unexpected type ... when generating a default value".
EXTENDS Integers, Sequences, FiniteSets, TLC, Option

VARIABLES
  \* @type: Int -> Str;
  myPc

\* @type: Seq((Int -> Str));
vars == <<myPc>>

ThreadInit(t) ==
  /\ myPc = [ x \in t |-> "Idle" ]

\* @type: Int => Some(Int) | None(UNIT);
operator1(x) ==
  IF (x % 2) = 0 THEN Some(x) ELSE None

\* @type: (Int, Int) => Some(Int) | None(UNIT);
operator2(x, y) ==
  IF ((x + y) % 2) = 0 THEN Some(x + y) ELSE None

\* @type: Int => Some(<<Int, Int>>) | None(UNIT);
problemOperator(self) ==
  LET q1 == operator1(self) IN
  IF IsNone(q1) THEN None ELSE (
    LET v1 == OptionGetOrElse(q1, self) IN
    OptionCase(operator2(self, v1),
      \* @type: Int => Some(<<Int, Int>>) | None(UNIT);
      LAMBDA v2: Some(<<v1, v2>>),
      LAMBDA u: None
    )
  )

\* @type: Int => Bool;
ThreadNext(self) ==
  /\ IsSome(problemOperator(self))
  /\ myPc' = [myPc EXCEPT ![self] = "abcdef"]

Threads == {1, 2, 3}
Init == ThreadInit(Threads)
Terminating ==
  /\ \A s \in Threads: myPc[s] = "Done"
  /\ UNCHANGED vars
Next ==
  \/ (\E self \in Threads: ThreadNext(self))
  \/ Terminating
=============================================================================

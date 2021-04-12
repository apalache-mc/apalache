---- MODULE MegaSpec1 -----
(*
 This specification contains plenty of TLA+ constructs to make sure that:
 (1) the type checker does not fail on them, and (2) all expressions are tagged with types.
 *)

EXTENDS Integers, Sequences, FiniteSets, Reals, Apalache, TLC
CONSTANTS
 \* @typeAlias: ELEM = Int;
 \* @type: ELEM;
 N

ASSUME(N > 42)

VARIABLES
   \* @type: Set([type: Str, val: ELEM]);
   msgs

\* LITERALS
TypeOfStr == "hello"
TypeOfInt == 10
TypeOfBool == FALSE
TypeOfIntSet == Int
TypeOfNatSet == Nat
TypeOfBoolSet == BOOLEAN
TypeOfStrSet == STRING

\* GENERAL OPERATORS
TypeOfEq == 1 = 2
TypeOfNeq == 1 /= 2
UserOper(x, y) == y + x
ApplyUserOper == UserOper(3, 4)
Choose == CHOOSE x \in { 1, 2, 3 }: x > 1
ChooseUnbounded == CHOOSE x: x > 1

\* LET-IN
A(x, y) ==
  LET Plus(a, b) == a + b IN
  Plus(x, y)

\* LAMBDA
B ==
  LET \* @type: (Int => Int) => Int;
      Foo(C(_)) == C(3)
  IN
  Foo(LAMBDA x: x + 1)

\* LOGIC
Equiv == FALSE <=> TRUE
Implies == FALSE => TRUE
And == FALSE /\ TRUE
Or == FALSE \/ TRUE
Not == ~FALSE
Exists == \E x \in { 1, 2, 3 }: x > 2
ExistsTuple == \E <<x, y>> \in { 1, 2, 3 } \X { 1 }: y > 2
Forall == \A x \in { 1, 2, 3 }: x > 2
ForallTuple == \A <<x, y>> \in { 1, 2, 3 } \X { 1 }: y > 2

\* SETS
\* @type: Set(Str);
EnumEmptySet == { }
EnumSet == { 1, 2, 3 }
RecSet == [ x: BOOLEAN, y: Int ]
SeqSet == Seq(Int)
SetIn(x) == x \in { 1, 2, 3 }
SetNotIn(x) == x \notin { 1, 2, 3 }
SetSubsetEq == { 1 } \subseteq { 1, 2 }
Subset == SUBSET { 1, 2, 3 }
BigUnion == UNION { {1}, {2} }
SetUnion == { 1, 2 } \cup { 2, 3 }
SetIntersect == { 1, 2 } \cap { 2, 3 }
SetMinus == { 1, 2 } \ { 2, 3 }
SetProd == { 1, 2 } \X { 2, 3 }
Filter == { x \in Int: x > 3 }
Filter2 == { <<x, y>> \in Int \X BOOLEAN: x > 3 }
Map == { 2 * x: x \in Int }
Map2 == { 2 * x: <<x, y>> \in Int \X BOOLEAN }

\* FUNCTIONS
Record == [ x |-> 2, y |-> TRUE ]
Tuple == <<3, "foo">>
\* @type: Seq(Int);
SeqAsTuple == <<3, 4>>
\* @type: (Int -> BOOLEAN) => BOOLEAN;
FunApp(f) == f[3]
\* @type: (Str -> Int) => Int;
FunAppStr(f) == f.num
\* @type: <<Int, Str>> => Str;
FunAppInt(f) == f[2]
\* @type: (Int -> Str) => Set(Int);
Domain(f) == DOMAIN f
FunCtor == [ x \in Int |-> 2 * x ]
FunCtor2 == [ x \in Int, y \in BOOLEAN |-> 2 * x ]
\* @type: (Int -> Str) => (Int -> Str);
FunExcept(f) == [f EXCEPT ![1] = "a"]
\* @type: (Int -> Str) => (Int -> Str);
FunExcept2(f) == [f EXCEPT ![1] = "a", ![3] = "b"]
\* @type: () => (Int -> Int);
rec[n \in Int] == IF n <= 1 THEN 1 ELSE n * rec[n - 1]
\* @type: () => (<<Int, Int>> -> Int);
rec2[m \in Int, n \in Int] == IF m + n <= 1 THEN 1 ELSE m * rec2[m - 1, n - 1]

\* CONTROL
Ite == IF TRUE THEN 2 ELSE 3
Case ==
  CASE FALSE -> 1 [] TRUE -> 3
CaseOther ==
  CASE FALSE -> 1 [] TRUE -> 3 [] OTHER -> 5

\* FiniteSets
TestIsFiniteSet == IsFiniteSet(BOOLEAN)
TestCardinality == Cardinality(BOOLEAN) = 2

\* Actions
TestPrime == msgs' = msgs
TestStutter == [TestPrime]_msgs
TestNoStutter == <<TestPrime>>_msgs
\* @type: <<Set([type: Str, val: Int])>>;
vars == <<msgs>>
TestUnchanged == UNCHANGED vars
TestComposition == TestPrime \cdot TestUnchanged

\* Temporal
Box == [] [TestPrime]_msgs
Diamond == <> <<TestPrime>>_msgs
Guarantees == TestIsFiniteSet -+-> TestCardinality
LeadsTo == TestIsFiniteSet ~> TestCardinality
WeakFairness == WF_msgs(TestPrime)
StrongFairness == SF_msgs(TestPrime)

\* Sequences
\* @type: Seq(Int) => Int;
SeqHead(seq) == Head(seq)
\* @type: Seq(Int) => Seq(Int);
SeqTail(seq) == Tail(seq)
\* @type: (Seq(Int), Int) => Seq(Int);
SeqAppend(seq, x) == Append(seq, x)
\* @type: (Seq(Int), Seq(Int)) => Seq(Int);
SeqConcat(seq1, seq2) == seq1 \o seq2
\* @type: Seq(Int) => Int;
SeqLen(seq) == Len(seq)
\* @type: Seq(Int) => Seq(Int);
SeqSubSeq(seq) == SubSeq(seq, 1, 2)
Even(n) == n % 2 = 0
\* @type: Seq(Int) => Seq(Int);
SeqSelectSeq(seq) == SelectSeq(seq, Even)

\* Arithmetic
IntUnaryMinus(x) == -x
IntPlus(x, y) == x + y
IntMinus(x, y) == x - y
IntMult(x, y) == x * y
IntDiv(x, y) == x \div y
IntMod(x, y) == x % y
IntExp(x, y) == x ^ y
IntLt(x, y) == x < y
IntLe(x, y) == x <= y
IntGt(x, y) == x > y
IntGe(x, y) == x >= y
IntDotDot(x, y) == x..y
RealDiv(x, y) == x / y

\* Apalache
\* @type: (Int -> Str) => Seq(Str);
Fas(f) == FunAsSeq(f, 3)

\* TLC
TlcPrint == Print("hello", 3)
TlcPrintT == PrintT("world")
TlcAssert == Assert(4 > 3, "no way")
TlcJavaTime == JavaTime
\* @type: () => Int;
TlcGet == TLCGet(3)
TlcSet == TLCSet(3, "a")
TlcColorGt == 1 :> "a"
TlcAtAt == (1 :> "a") @@ (2 :> "b")
TlcPermutations == Permutations({1, 2})
\* @type: (Seq(Int), ((Int, Int) => Bool)) => Seq(Int);
TlcSortSeq(seq, F(_, _)) == SortSeq(seq, F)
TlcRandomElement == RandomElement({1, 2})
\* @type: () => Int;
TlcAny == Any
TlcToString == ToString(12)
TlcEval == TLCEval(10)
===============================================================================
---------- MODULE TestInlining ----------

EXTENDS Integers, Apalache

TestLetSimple == 
  LET A(p) == p + 1
  IN A(0) = 1

GLOBAL_A1(p) == p + 1

TestGlobalSimple ==
  GLOBAL_A1(0) = 1

TestNestedLet ==
  LET P(x,y) == 
    LET Q(z) == z + y 
    IN Q(x)
  IN P(1,2) = 3

GLOBAL_Q(z) == z + 1
GLOBAL_P(x) == GLOBAL_Q(x) + 1

TestLinearDep ==
  GLOBAL_P(1) = 3

TestKeepNullary == 
  LET A == 1
      B(x) == 2
  IN A + B(0) = 3 

TestPassByName == 
  LET A(x,y) == 1
  IN ApaFoldSet(A, 0, 1..3) = 1

TestPassLambda == 
  ApaFoldSet(LAMBDA x, y: x + y, 0, 1..3) = 6

\* @type: (Int, Int) => Int;
GLOBAL_A2(x, y) == 
    LET \* @type: (Int, Int) => Int;
        F(old, new) == new
    IN ApaFoldSeqLeft(F, x, <<y>>) \* = y

TestNestedPassByName ==
  ApaFoldSeqLeft(GLOBAL_A2, 0, <<1>>) = 1

GLOBAL_A3 == 1

TestNullaryGlobalInline ==
  GLOBAL_A3 = 1

TestOperAsArg ==
  LET B == 0 IN 
  LET A(x) == x IN
  A(B) = 0

TestMixedScope ==
  LET 
    A(x) == 
      LET F(p,q) == x
      IN ApaFoldSeqLeft(F, 0, <<1>>)
  IN A(2) = 2

TestHONoLambda ==
  LET 
    \* @type: (Int => Int) => Int;
    A(F(_)) == F(1)
  IN LET
    P(p) == p + 1
  IN A(P) = 2

\* @type: ((a,a) => b, a) => b;
GLOBAL_A4(F(_,_), e) == F(e,e)
GLOBAL_B1(x) == 
  LET Plus(a,b) == a + b
  IN GLOBAL_A4(Plus, x)

TestDoubleHO ==
  LET G(F(_)) == F(1) IN
  G(LAMBDA p: GLOBAL_B1(p)) = 2

TestPolymorphism == 
  LET 
    \* @type: (a => b, a) => b;
    App(X(_), p) == X(p)
  IN LET 
    \* @type: (Int) => Int;
    X1(p) == p + 1
    \* @type: (Bool) => Bool;
    X2(b) == ~b
  IN App(X2, App(X1, 1) = 1 )

TestLongChain == 
  LET
    A0(x) == x + x
  IN LET
    A1(x) == A0(x) + x
  IN LET
    A2(x) == A1(x) + x
  IN LET
    A3(x) == A2(x) + x
  IN LET
    A4(x) == A3(x) + x
  IN LET
    A5(x) == A4(x) + x
  IN A5(1) = 7


Init == TRUE

Next == TRUE

AllTests ==
  /\ TestLetSimple
  /\ TestGlobalSimple
  /\ TestNestedLet
  /\ TestLinearDep
  /\ TestKeepNullary
  /\ TestPassByName
  /\ TestPassLambda
  /\ TestNestedPassByName
  /\ TestNullaryGlobalInline
  /\ TestOperAsArg
  /\ TestMixedScope
  /\ TestHONoLambda
  /\ TestDoubleHO
  /\ TestPolymorphism
  /\ TestLongChain

====================

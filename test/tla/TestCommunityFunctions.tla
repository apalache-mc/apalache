-------------------- MODULE TestCommunityFunctions ----------------------------
(*
 * Functional tests for operators over functions in the community modules.
 * We introduce a trivial state machine and write tests as state invariants.
 *
 * These tests are derived from:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/tests/FunctionsTests.tla
 *)
EXTENDS Integers, Apalache, Functions

Init == TRUE
Next == TRUE

\* @type: Set(Int);
EmptySet == {}

\* @type: Int -> Int;
EmptyFun == [x \in {} |-> x]

AddToSet(x, y) == { x } \union y

(* TESTS *)
TestRestrict ==
    LET in == [ x \in 2..6 |-> x + 1 ] IN
    LET out == [ x \in { 3, 5 } |-> x + 1 ] IN
    Restrict(in, DOMAIN out) = out

TestRange ==
    LET in == [ x \in 2..6 |-> x + 1 ] IN
    Range(in) = 3..7

TestIsInjectiveEmpty ==
    IsInjective(EmptyFun)

TestIsInjective1 ==
    IsInjective([x \in { 1 } |-> x])

TestIsInjective3 ==
    IsInjective([x \in 1..3 |-> x])

TestIsInjective11 ==
    ~IsInjective([x \in 1..2 |-> 1])

TestIsInjective1123 ==
    ~IsInjective([ x \in 1..4 |-> IF x > 2 THEN x ELSE 1 ])

TestIsInjective1to10 ==
    IsInjective([x \in 1..10 |-> x])

TestIsInjective1to10set ==
    IsInjective([x \in 1..10 |-> {x}])

TestIsInjective1to10to123 ==
    ~IsInjective([x \in 1..10 |-> { 1, 2, 3 }])

TestFoldFunction121 ==
    LET f == SetAsFun({ <<1, 1>>, <<2, 2>>, <<3, 1>> }) IN
    FoldFunction(AddToSet, EmptySet, f) = { 1, 2 }

TestFoldFunctionOnSet ==
    LET f == [ i \in 1..2 |-> i ] IN
    FoldFunctionOnSet(AddToSet, EmptySet, f, {}) = {}

TestFoldFunction1to9 ==
    FoldFunction(AddToSet, EmptySet, [n \in 1..9 |-> n]) = 1..9

TestFoldFunctionOnSet1to9 ==
    FoldFunctionOnSet(AddToSet, EmptySet, [n \in 1..9 |-> n], {}) = {}

TestFoldFunctionOnSet2to8 ==
    FoldFunctionOnSet(AddToSet,
        EmptySet, [n \in 1..9 |-> n], 2..8) = 2..8

TestIsInjectiveEquiv ==
    LET \* @type: (a -> b) => Bool;
        IsInjectivePure(f) ==
        \A a, b \in DOMAIN f:
            f[a] = f[b] => a = b
    IN
    /\ \A f \in [{0, 1, 2} -> {0, 1, 2, 3}]:
          IsInjectivePure(f) = IsInjective(f)
    /\ \A f \in [{"a", "b", "c"} -> {0, 1, 2, 3}]:
          IsInjectivePure(f) = IsInjective(f)
    /\ \A f \in [{0, 1, 2, 3} -> {"a", "b", "c"}]:
          IsInjectivePure(f) = IsInjective(f)        

TestAntiFunction ==
    LET input == SetAsFun({ <<1, "a">>, <<2, "b">>, <<3, "c">> }) IN
    LET output == SetAsFun({ <<"a", 1>>, <<"b", 2>>, <<"c", 3>> }) IN
    AntiFunction(input) = output

TestInverseEquiv ==
    LET InversePure(f, S, T) ==
        [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]
    IN
    /\ \A f \in [{0, 1, 2} -> {0, 1, 2, 3}]:
        IsInjective(f)
            => InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
    /\ \A f \in [{"a", "b", "c"} -> {0, 1, 2, 3}]:
        IsInjective(f)
            => InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
    /\ \A f \in [{0, 1, 2, 3} -> {"a", "b", "c"}]:
        IsInjective(f)
            => InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)

TestInjection ==
    LET f == [ x \in 2..10 |-> 2 * x ] IN
    f \in Injection(DOMAIN f, Range(f))

TestNotInjection ==
    LET f == [ x \in 2..10 |-> x \div 2 ] IN
    f \notin Injection(DOMAIN f, Range(f))

TestExistsInjection ==
    ExistsInjection(1..3, 5..9)

TestNotExistsInjection ==
    ~ExistsInjection(1..10, 5..7)

TestSurjection ==
    LET f == [ x \in 2..10 |-> x \div 2 ] IN
    f \in Surjection(DOMAIN f, Range(f))

TestNotSurjection ==
    LET f == [ x \in 2..10 |-> x \div 2 ] IN
    ~(f \in Surjection({ 1 } \union (DOMAIN f), Range(f)))

TestExistsSurjection ==
    ExistsSurjection(1..3, 5..7)

TestNotExistsSurjection ==
    ~ExistsSurjection(1..3, 5..9)

TestBijection ==
    LET f == [ x \in 2..10 |-> 2 * x ] IN
    f \in Bijection(DOMAIN f, Range(f))

TestNotBijection ==
    LET f == [ x \in 2..10 |-> x \div 2 ] IN
    f \notin Bijection(DOMAIN f, Range(f))

TestExistsBijection ==
    ExistsBijection(1..3, 5..7)

TestNotExistsBijection ==
    ~ExistsBijection(1..4, 5..6)

TestNotExistsBijection2 ==
    ~ExistsBijection(1..4, 5..10)

AllTests ==
    /\ TestRestrict
    /\ TestRange
    /\ TestIsInjectiveEmpty
    /\ TestIsInjective1
    /\ TestIsInjective3
    /\ TestIsInjective11
    /\ TestIsInjective1123
    /\ TestIsInjective1to10
    /\ TestIsInjective1to10set
    /\ TestIsInjective1to10to123
    /\ TestFoldFunction121
    /\ TestFoldFunctionOnSet
    /\ TestFoldFunction1to9
    /\ TestFoldFunctionOnSet1to9
    /\ TestFoldFunctionOnSet2to8
    /\ TestIsInjectiveEquiv
    /\ TestAntiFunction
    /\ TestInverseEquiv
    /\ TestInjection
    /\ TestNotInjection
    /\ TestExistsInjection
    /\ TestNotExistsInjection
    /\ TestSurjection
    /\ TestNotSurjection
    /\ TestExistsSurjection
    /\ TestNotExistsSurjection
    /\ TestBijection
    /\ TestNotBijection
    /\ TestExistsBijection
    /\ TestNotExistsBijection
    /\ TestNotExistsBijection2

===============================================================================

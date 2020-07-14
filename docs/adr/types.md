# ADR 1: types and type annotations

It is good to have a number of different opinions here. As I can see, we
actually have three issues, not one (I initially have put emphasis only on the
third issue):

1. How to encode types in TLA+.
1. How to encode type annotations.
1. How to display inferred types.

## 1. How to encode types in TLA+

Everybody has a different opinion here. I agree that it would be cool to use
the native TLA+ constructs to express types. My initial approach, in which
types are specified as strings over the type grammar, may be seen as a hack.
However, it clearly distinguishes TLA+ from types, which has some merits. The
biggest problem I personally have with TLA+ is that it mixes a lot of good and
interesting concepts in a uniform logic soup. After I have learned how to separate
potatoes from beans in that soup, I started to appreciate TLA+ :-)

### 1.1. TypeOK syntax

The only way to write types in the `TypeOK` style is by set membership.
For instance:

* `x` is an integer: `x \in Int`
* `f` is a function from an integer to an integer: `f \in [Int -> Int]`
* `f` is a function from a set of integers to a set of integers:
    `f \in [SUBSET Int -> SUBSET Int]`
* `r` is a record that has the fields `a` and `b`, where `a` is an integer
    and `b` is a string: `r \in [a: Int, b: STRING]`
* `f` is a set of functions from a tuple of integers to an integer:
    `f \in SUBSET [Int \X Int -> Int]`
* `Foo` is an operator of an `Int` and `STRING` that returns an `Int`:
    `\A a \in Int: \A b \in STRING: Foo(a, b) \in Int`
* `Bar` is a higher-order operator that takes an operator that takes
    an `Int` and `STRING` and returns an `Int`, and returns a `BOOLEAN`.
    We cannot quantify over operators. __Anybody has an idea how to write that down?__

I personally find this syntax obfuscated, as it inevitably requires us to write
types as sets of values.

### 1.2. Types as terms

A classical way of writing types is by using logical terms (or algebraic datatypes).
To this end, we can define a special module `Types.tla`:

```tla
---- MODULE Types ----
\* Types as terms. The right-hand side of an operator does not play a role,
\* but we define it as the corresponding set of values.
\* Alternatively, we could just define tuples of strings in rhs.

\* a type annotation operator that omits the type
value <: type == value

\* the integer type
IntT == Int
\* the Boolean type
BoolT == BOOLEAN
\* the string type
StrT == STRING

\* a set type
SetT(elemT) == SUBSET elemT
\* a function type
FunT(fromT, toT) == [fromT -> toT]
\* a sequence type
SeqT(elemT) == Seq(elemT)

\* tuple types
Tup0T == {}
Tup1T(t1) == t1
Tup2T(t1, t2) == t1 \X t2
Tup3T(t1, t2, t3) == t1 \X t2 \X t3
\* and so on, e.g., Scala has 26 tuples. how many do we like to have?

\* Record types. We assume that field names are alphabetically ordered.
\* We cannot use record-set notation here,
\* as the field names are parameters. So I gave up here on giving corresponding sets.
Rec1T(f1, t1) == <<"Rec1", f1, t1>>
Rec2T(f1, t1, f2, t2) == <<"Rec2", f1, t1, f2, t2>>
Rec3T(f1, t1, f2, t2, f3, t3) == <<"Rec3", f1, t1, f2, t2, f3, t3>>
\* and so on

\* Operator types. No clear set semantics.
\* Note that the arguments can be operators as well!
\* So this approach gives us higher-order operators for free.
Oper0T(resT) == <<"Oper0", resT>>
Oper1T(arg1T, resT) == <<"Oper1", arg1T, res1T>>
Oper2T(arg1T, arg2T, resT) == <<"Oper2", arg1T, arg2T, res1T>>
\* and so on
======================
```

Assuming that we have some syntax for writing down that `x` has type `T`,
e.g., by writing `x <: T`, we can write the above examples as follows:

* `x` is an integer: `x <: IntT`
* `f` is a function from an integer to an integer: `f <: FunT(IntT, IntT)`
* `f` is a function from a set of integers to a set of integers:
    `f <: FunT(SetT(IntT), SetT(IntT))`
* `r` is a record that has the fields `a` and `b`, where `a` is an integer
    and `b` is a string: `r <: Rec2T("a", IntT, "b", StrT)`
* `f` is a set of functions from a tuple of integers to an integer:
    `f <: SetT(FunT(Tup2T(IntT, IntT), IntT))`
* `Foo` is an operator of an `Int` and `STRING` that returns an `Int`:
    `\A a: \A b: Foo(a, b) <: Oper2(IntT, StrT, IntT)`.

  * __Here it gets tricky, as the TLA+ syntax does not allow us to
    mention an operator by name without applying it.__

* `Bar` is a higher-order operator that takes an operator that takes
    an `Int` and `STRING` and returns an `Int`, and returns a `BOOLEAN`.
    `\A a, b, c: Bar(LAMBDA a, b: c) <: Oper1(Oper2(IntT, StrT, IntT), BoolT)`.

  * __Here we have to pull lambda operators, but at least it is possible to write
    down a type annotation.__


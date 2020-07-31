# RFC 001: types and type annotations

It is good to have a number of different opinions here. As I can see, we
actually have three issues, not one (I initially have put emphasis only on the
third issue):

1. How to write types in TLA+.
1. How to write type annotations (as a user).
1. How to display and use inferred types.

## 1. How to write types in TLA+

Everybody has a different opinion here. I agree that it would be cool to use
the native TLA+ constructs to express types. My initial approach, in which
types are specified as strings over the [type grammar](#typesAsStrings), may be seen
as a hack.  However, it clearly distinguishes TLA+ from types, which has some
merits. The biggest problem I personally have with TLA+ is that it mixes a lot
of good and interesting concepts in a uniform logic soup. After I have learned
how to separate potatoes from beans in that soup, I started to appreciate TLA+
:-)

<a name="typesAsTypeOk"></a>
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

<a name="typesAsTerms"></a>
### 1.2. Types as terms

A classical way of writing types is by using logical terms (or algebraic datatypes).
To this end, we can define a special module `Types.tla`:

```tla
---- MODULE Types ----
\* Types as terms. The right-hand side of an operator does not play a role,
\* but we define it as the corresponding set of values.
\* Alternatively, we could just define tuples of strings in rhs.

\* a type annotation operator that erases the type
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

<a name="typesAsStrings"></a>
### 1.3. Types as strings

Let us introduce the following grammar for types:

```
T ::= var | Bool | Int | Str | T -> T | Set(T) | Seq(T) |
      <<T, ..., T>> | [h_1 |-> T, ..., h_k |-> T] | (T, ..., T) => T
```      

In this grammar, `var` stands for a type variable, which can be instantiated with
concrete variable names such as `a`, `b`, `c`, etc., whereas `h_1`,...,`h_k` are
field names. The rule `T -> T` defines a function, while the rule
`(T, ..., T) => T` defines an operator.

Assuming that we have some syntax for writing down that `x` has type `T`,
e.g., by writing `isType("x", "T")`, we can write the above examples as follows:

* `x` is an integer: `isType("x", "Int")`.
* `f` is a function from an integer to an integer: `isType("f", "Int -> Int")`.
* `f` is a function from a set of integers to a set of integers:
    `isType("f", "Set(Int) -> Set(Int))"`.
* `r` is a record that has the fields `a` and `b`, where `a` is an integer
    and `b` is a string: `isType("r", "[a |-> Int, b |-> Str])"`.
* `f` is a set of functions from a tuple of integers to an integer:
    `isType("f", "Set(<<Int, Int>> -> Int))"`.
* `Foo` is an operator of an `Int` and `STRING` that returns an `Int`:
    `isType("Foo", "(Int, Str) => Int")`.

* `Bar` is a higher-order operator that takes an operator that takes
    an `Int` and `STRING` and returns an `Int`, and returns a `BOOLEAN`:
    `isType("Bar", "((Int, Str) => Int) => Bool")`.

__Note:__ We have to pass names as strings, as it is impossible to pass operator
    names, e.g., `Foo` and `Bar` in other operators, unless `Foo` and `Bar`
    are nullary operators and `isType` is a higher-order operator.


## 2. How to write type annotations (as a user)

__Note__: This question is not a priority, as we do not expect the user to
write type annotations. However, it would be good to have a solution, as sometimes
users want to write types.

Again, we have plenty of options and opinions here:

1. Write type annotations by calling a special operator like `<:` or `|=`.
1. Write type annotations as assumptions.
1. Write type annotations in comments.
1. Write type annotations as operator definitions.

### 2.1. Type annotations with a special operator

This is the current approach in Apalache. One has to define an operator, e.g., `<:`:

```tla
value <: type == value
```

Then an expression may be annotated with a type as follows:

```tla
VARIABLE S
Init ==
  S = {} <: {Int}
```

__Pros__:
 * Intutive notation, similar to programming languages.

__Cons__:

 * This approach works well for expressions. However, it is not clear how to extend
   it to operators.
 * This notation is more like type clarification, rather than a type annotation.
   Normally types are specified for names, that is, constants, variables, functions,
   operators, etc.
 * Same expression may be annotated in a Boolean formula. What shall we do, if the
   user writes: `x <: BOOLEAN \/ x <: Int`?

__Note:__ The current approach has an issue. If one declares the operator `<:` in
a module `M` and then uses an unnamed instance `INSTANCE M` in a module `M2`,
then `M` and `M2` will clash on the operator `<:`. We should define the operator
once in a special module `Types` or `Apalache`.

<a name="annotationsAsAssumptions"></a>
### 2.2. Type annotations as assumptions

One can use TLA+ syntax to write assumptions and assertions about the types.
We are talking only about type assumptions here.
The similar approach can be used to write theorems about types. 
Consider the following specification:

```tla
EXTENDS Sequences
CONSTANTS Range
VARIABLES list

Mem(e, es) ==
  \E i \in DOMAIN es:
    e = es[i]
```

In this example, the operator `Mem` is polymorphic, whereas the types of `Range`
and `list` are parameterized.  If the user wants to
restrict the types of constants, variables, and operators, they could write (using the
[TypeOK syntax](#typesAsTypeOk)):

```tla
ASSUME(Range \in SUBSET Int)
ASSUME(list \in Seq(Int))
ASSUME(\A e \in Int, \A es \in Seq(Int): Mem(e, es) \in BOOLEAN)
```

SANY parser only accepts the first assumption in the above
example. __The two other assumptions are rejected by the parser, as they
refer to non-constant values.__

Moreover, using the proof syntax of
[TLA+ Version 2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf),
we can annotate the
types of variables introduced inside the operators.  For instance, we could
label the name `i` as follows:

```tla
Mem(e, es) ==
  \E i \in DOMAIN es:
    e = es[i_use :: i]
```

And then write:

```tla
ASSUME(\A e, es, i: Mem(e, es)!i_use(i) \in Int)
```

__Pros__:

 * The assumptions syntax is quite appealing, when writing types of
    CONSTANTS, VARIABLES, and top-level operators.

__Cons__:

 * The syntax gets verbose and hard to write, when writing types of
   LET-IN operators and bound variables.
 * It is not clear how to extend this syntax to higher-order operators.
 * __One cannot write assumptions about state variables.__

### 2.3. Type annotations in comments
 
This solution basically gives up on TLA+ syntax and introduces a special
syntax à la javadoc for type annotations:

```tla
EXTENDS Sequences
CONSTANTS Range \*@ Range: Set(Int)
VARIABLES list  \*@ list: Seq(Int)

Mem(e, es) ==
\*@ Mem: (Int, Seq(Int)) => Bool
  \E i \in DOMAIN es:
    \*@ i: Int
    e = es[i]
```

We have not come up with a good syntax for these annotaions. The above
example demonstrates one possible approach.

__Pros__:

  * Non-verbose, simple syntax
  * Type annotations do not stand in the way of the specification author
  * Type annotations may be collapsed, removed, etc.
  * If we have an annotation preprocessor, we can use it for other
    kinds of annotations

__Cons__:

  * As we give up on the TLA+ syntax, TLA+ Toolbox will not help us
    (though it is not uncommon for IDEs to parse javadoc annotations,
     so there is some hope)
  * The users have to learn new syntax for writing type annotations and types
  * We have to write an annotation preprocessor

### 2.4. Type annotations as operator definitions

Operators definitions and LET-IN definitions can be written almost anywhere in
TLA+. Instead of writing in-comment annotations, we can write annotations
with operator definitions (assuming [types as strings](#typesAsStrings),
but this is not necessary):

```tla
EXTENDS Sequences
CONSTANTS Range
Range_type == "set(z)"

VARIABLES list
list_type == "seq(z)"

Mem(e, es) ==
  LET Mem_type == "<a, seq(a)> => Bool" IN
  \E i \in DOMAIN es:
    LET i_type == "Int" IN
    e = es[i]

Init ==
  LET Init_type == "<> => Bool" IN
  list = <<>>

Next ==
  LET Next_type == "<> => Bool" IN
  \E e \in Range:
    LET e_type == "set(z)" IN
    list' = Append(list, e)
```

__Pros:__

 * No need for a comment preprocessor,
    easy to extract annotations from the operator definitions

__Cons:__

 * Fruitless operator definitions
 * Looks like a hack


## 3. How to display and use inferred types

__TBD__

Basically, use [Language Server
Protocol](https://microsoft.github.io/language-server-protocol/) and introduce
THEOREMs (similar to [types as assumptions](#annotationsAsAssumptions)).

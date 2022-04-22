# ADR-002: types and type annotations

| authors                                | revision | revision date  |
| -------------------------------------- | --------:| --------------:|
| Shon Feder, Igor Konnov, Jure Kukovec  |        5 | April 08, 2022 |

*This is an architectural decision record. For user documentation, check the
[Snowcat tutorial][] and [Snowcat HOWTO][].*

This is a follow up of [RFC-001](./001rfc-types.md), which discusses plenty of
alternative solutions. In this __ADR-002__, we fix one solution that seems to be
most suitable. The interchange format for the type inference tools will be
discussed in a separate ADR.

1. How to write types in TLA+ (Type System 1).
1. How to write type annotations (as a user).

This document assumes that one can write a simple type checker that computes
the types of all expressions based on the annotations provided by the user.
Such an implementation is provided by the type checker Snowcat.
See the [manual chapter](../apalache/typechecker-snowcat.md) on Snowcat.

In contrast, the [type inference
algorithm](https://github.com/informalsystems/apalache/tree/types) by @Kukovec
is fully automatic and thus it eliminates the need for type annotations.
Jure's algorithm is using Type System 1 too. The type inference algorithm
is still in the prototype phase.

System engineers often want to write type annotations and quickly check types
when writing TLA+ specifications. This document is filling this gap.

## 1. How to write types in TLA+

### 1.1. Type grammar (Type System 1, or TS1)

We simply write types as strings that follow the type grammar:

```
T ::=   'Bool' | 'Int' | 'Str'
      | T '->' T
      | 'Set' '(' T ')'
      | 'Seq' '(' T ')'
      | '<<' T ',' ...',' T '>>'
      | '[' field ':' T ',' ...',' field ':' T ']'
      | '(' T ',' ...',' T ')' '=>' T
      | typeConst
      | typeVar
      | '(' T ')'

field     ::= <an identifier that matches [a-zA-Z_][a-zA-Z0-9_]*>

typeConst ::= <an identifier that matches [A-Z_][A-Z0-9_]*>

typeVar   ::= <a single letter from [a-z]>
```

The type rules have the following meaning:
- The rules `Bool`, `Int`, `Str` produce primitive types:
    the Boolean type, the integer type, and the string type, respectively.
- The rule `T -> T` produces a function.
- The rule `Set(T)` produces a set type over elements of type `T`.
- The rule `Seq(T)` produces a sequence type over elements of type `T`.
- The rule `<<T, ..., T>>` produces a tuple type over types that
    are produced by `T`. *Types at different positions may differ*.
- The rule `[field: T, ..., field: T]` produces a record type over types that
    are produced by `T`. *Types at different positions may differ*.
- The rule `(T, ..., T) => T` defines an operator whose result type and parameter types are produced by `T`.
- The rule `typeConst` defines an uninterpreted type (or a reference to a type alias), look for an explanation below.
- The rule `typeVar` defines a type variable, look for an explanation below.

Importantly, a multi-argument function always receives a tuple, e.g., `<<Int,
Bool>> -> Int`, whereas a single-argument function receives the type of its
argument, e.g., `Int -> Int`.  The arrow `->` is right-associative, e.g., `A ->
B -> C` is understood as `A -> (B -> C)`, which is consistent with programming
languages. If you like to change the priority of `->`, use parentheses, as
usual.  For example, you may write `(A -> B) -> C`.

An operator always has the types of its arguments inside `(...)`, e.g., `(Int, Bool) => Int` and `() => Bool`. If a
type `T` contains a type variable, e.g.,
`a`, then `T` is a polymorphic type, in which `a` can be instantiated with a monotype (a variable-free term). Type
variables are useful for describing the types of polymorphic operators. Although the grammar accepts an operator type
that returns an operator, e.g., `Int => (Int => Int)`, such a type does not have a meaningful interpretation in TLA+.
Indeed, TLA+ does not allow operators to return other operators.

A type constant should be understood as a type we don't know and we don't want to know, that is, an uninterpreted type.
Type constants are useful for fixing the types of CONSTANTS and using them later in a specification. Two different type
constants correspond to two different -- yet uninterpreted -- types. If you
know [Microsoft Z3](https://github.com/Z3Prover/z3), a type constant can be understood as an uninterpreted sort in SMT.
Essentially, values of an uninterpreted type can be only checked for equality.

Another use for a type constant is referring to a type alias, see [Section 1.2](#defTypeAlias). This is purely a
convenience feature to make type annotations more concise and easier to maintain. We expect that only users will write
type aliases: tools should always exchange data with types in the alias-free form.

**Examples.**

* `x` is an integer. Its type is `Int`.
* `f` is a function from an integer to an integer. Its type is `Int -> Int`.
* `f` is a function from a set of integers to a set of integers.
    Its type is `Set(Int) -> Set(Int)`.
* `r` is a record that has the fields `a` and `b`, where `a` is an integer
    and `b` is a string. Its type is `[a: Int, b: Str]`.
* `F` is a set of functions from a pair of integers to an integer.
   Its type is `Set(<<Int, Int>> -> Int)`.
* `Foo` is an operator of an integer and of a string that returns an integer.
   Its type is  `(Int, Str) => Int`.
* `Bar` is a higher-order operator that takes an operator that takes
    an integer and a string and returns an integer, and returns a Boolean.
   Its type is  `((Int, Str) => Int) => Bool`.
* `Baz` is a polymorphic operator that takes two arguments of the same type
    and returns a value of the type equal to the types of its arguments.
   Its type is `(a, a) => a`.
* `Proc` and `Faulty` are sets of the same type.
   Their type is `Set(PID)`.

<a id="defTypeAlias"></a>
### 1.2. Type aliases

The grammar of `T` includes one more rule for defining a type alias:

```
A ::= typeConst "=" T
```

This rule binds a type (produced by `T`) to a name (produced by `typeConst`). As you can see from the definition
of `typeConst`, the name should be an identifier in the upper case. The type checker should use the bound type instead
of the constant type. For examples, see [Section 2.4](#useTypeAlias).

<a id="rows"></a>
### <a id="ts-1.2"></a>1.3. Type System 1.2, including precise records, variants, and rows

**This is work in progress.** You can track the progress of this work in [Issue
401][]. Once this work is complete, we will switch to Type System 1.2.

As discussed in [ADR014][], many users expressed the need for precise type
checking for records in Snowcat. Records in untyped TLA+ are used in two
capacities: as plain records and as variants. While the technical proposal is
given in [ADR014][], we discuss the extension of the type grammar in this
ADR-002.  To this end, we extend the grammar with new records, variants, and
rows as follows:

```
// Type System 1.2
T2 ::=
    // all types of Type System 1
    T
    // A new record type with a fully defined structure.
    // The set of fields may be empty.
    | '{' field ':' T2 ',' ...',' field ':' T2 '}'
    // A new record type with a partially defined structure
    // (the type variable should be a 'row').
    // The set of fields may be empty.
    | '{' field ':' T2 ',' ...',' field ':' T2 ',' typeVar '}'
    // A variant that contains several options.
    | variantOption '|' ... '|' variantOption
    // A variant of undefined structure (the type variable should be a 'row')
    | 'Variant' '(' typeVar ')'
    // An empty variant
    | 'Variant' '(' ')'

variantOption ::=
    // A variant option with a fully defined structure.
    | { tag: stringLiteral, field: T2, ..., field: T2 }
    // a variant option with a partially defined structure
    //   (a variant option over a row).
    | { tag: stringLiteral, field: T2, ..., field: T2, typeVar }

// Special syntax for the rows, which is internal to the type checker.
row ::=
    // A row with a fully defined structure.
    | '(|' field ':' T2 '|' ...'|' field ':' T2 '|)'
    // A row with a partially defined structure (ending with a row).
    | '(|' field ':' T2 '|' ...'|' field ':' T2 '|' typeVar '|)'
```

**Examples.**

* `r1` is a record that has the fields `a` and `b`, where `a` is an integer and
  `b` is a string. Its type is `{ a: Int, b: Str }`.

* `r2` is a record that has the fields `a` of type `Int` and `b` of type `Str`
  and other fields, whose precise structure is captured with a type variable
  `c`. The type of `r2` is `{ a: Int, b: Str, c }`.  More precisely, the
  variable `c` should be a row. For instance, `c` can be equal to the row `(|
  f: Bool | g: Set(Int) |)`; in this case, `r2` would be a record of type `{ a:
  Int, b: Str, f: Bool, g: Set(Int) }`.

* `v1` is a variant that has one of the two possible shapes:
 
   - It has the fields `tag` of type `Str` and `a` of type `Int` (if the field
     `tag` is equal to `"A"`).

   - It has the fields `tag` of type `Str` and `b` of type `Bool` (if the field
     `tag` is equal to `"B"`).

* `v2` is an empty variant, which admits no options. It has the type
  `Variant()`.

* `v3` is a variant whose structure is defined by the type variable `b`.
   The type of `v3` is `Variant(b)`. Note that `b` type variable should be
   a row. For instance, it can be equal to the type `(| A: { tag: Str, f: Int }
   | B: { tag: Str, g: Str } |)`.

Note that this syntax encapsulates rows in records and variants. We introduce
the syntax for row types for completeness. Most likely, the users will never
see messages that mention rows explicitly, without referring to records or
variants. 

<a id="comments"></a>
### 1.4. Comments inside types

When you introduce records that have dozens of fields, it is useful to explain
those fields right in the type annotations. For that reason, the type lexer
supports one-line comments right in the type definitions. The following
text presents a type definition that contains comments:

```
// packets are stored in a set
Set([
  // unique sequence number
  seqno: Int,
  // payload hash
  payloadHash: Str
])
```

The parser only supports one-line comments that starts with `//`. Since type
annotations are currently written inside TLA+ comments, we feel that more
complex comments would complicate the matters.

### 1.5. Discussion

Our type grammar presents a minimal type system that, in our understanding,
captures all interesting cases that occur in practice. Obviously, this type
system considers ill-typed some perfectly legal TLA+ values. For instance, we
cannot assign a reasonable type to `{1, TRUE}`.

**Sets of records in Type System 1.**
We can assign a reasonable type to `{[type |-> "1a", bal |-> 1], [type
|-> "2a", bal |-> 2, val |-> 3]}`, a pattern that often occurs in practice,
e.g., see
[Paxos](https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla).
The type of that set will be `Set([type: Str, bal: Int, val: Int])`, which is
probably not what you expected, but it is the best type we can actually compute
without having algebraic datatypes in TLA+. It also reminds the user that one
better tests the field `type` carefully.

**Sets of records in Type System 1.2.** Consider the following set:

```tla
{[tag |-> "1a", bal |-> 1],
 [tag |-> "2a", bal |-> 2, val |-> 3]}
```

In Type System 1.2 ([Section 1.3](#ts-1.2)), this set has the type of a set over a variant
type:

```tla
Set({ tag: "1a", bal: Int } | { tag: "2a", bal: Int, val: Int })
```

The value of the field `tag` serves as a type tag. However, we have to fix a
set of patterns that turn a variant type into a precise record type. In untyped
TLA+, such pattern is a set comprehension, e.g., `{ r \in S: r.tag = "1a" }`.
In the typed version, we define a minimal set of operators over variants in the
module
[Variants.tla](https://github.com/informalsystems/apalache/blob/unstable/src/tla/Variants.tla).
For instance, instead of writing the set comprehension, we have to use a filter
over a set of variants: `FilterByTag(S, "1a")`.

**Other type systems.**
Type System 1 is also very much in line with the [type system by Stephan Merz and Hernan Vanzetto](https://dblp.org/search?q=Automatic+Verification+of+%7BTLA%7D+%2B+Proof+Obligations+with+%7BSMT%7D+Solvers),
which is used internally by
[TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) when translating proof obligations in SMT. We introduce
types for user-defined operators, on top of their types for TLA+ expressions that do not contain user-defined operators.

We expect that this type system will evolve in the future. That is why we call
it __Type System 1__. [Section 1.3](#ts-1.2) presents its extension to __Type System
1.2__. Feel free to suggest __Type System 2.0__ :-)

## 2. How to write type annotations (as a user)

In the following, we discuss how to annotate different TLA+ declarations.

*In the previous version of this document, we defined two operators:
`AssumeType(_, _)` and `_ ## _`. They are no longer needed as we have introduced [Code annotations](./004adr-annotations.md).*

### 2.1. Annotating CONSTANTS and VARIABLES

Simply write an annotation `@type: <your type>;` in a comment that precedes the declaration of a constant declaration or
a variable. See the following example:

```tla
CONSTANT
  \* @type: Int;
  N,
  \* @type: Set(ID);
  Base

VARIABLE
  \* @type: ID;
  x,
  \* @type: Set(ID);
  S
```

__Why don't we use THEOREMs?__ It is tempting to declare the types of variables
as theorems. For example:

```tla
THEOREM N <: "Int"
```

However, this theorem must be proven. A *type inference engine* would be able
to infer the type of `N` and thus state such a theorem. However, with type
assumptions, the user merely states the variable types and the *type checker*
has a simple job of checking type consistency and finding the types of the
expressions.

## 2.2. Annotating operators

Again, write a type annotation `@type: <your type>;` in a comment that precedes the operator declaration. For example:

```tla
\* @type: (a, Seq(a)) => Bool;
Mem(e, es) ==
    (e \in {es[i]: i \in DOMAIN es})
```

Higher-order operators are also easy to annotate:

```tla
\* @type: ((a) => Bool, Seq(a)) => Int;
Find(Pred(_), es) ==
    IF \E i \in DOMAIN es: Pred(es[i])
    THEN CHOOSE i \in DOMAIN es: Pred(es[i])
    ELSE -1
```

The following definition declares a (global) function, not an
operator. However, the annotation syntax is quite similar to that of the
operators (note though that we are using `->` instead of `=>`):

```tla
\* @type: (a -> b) -> Int;
CardDomain[f \in T] ==
    LET \* @type: Set(a);
        \* we could also write: "() => Set(a)" instead of just "Set(a)"
        D == DOMAIN f
    IN LET \* @type: (Int, Int) => Int;
           PlusOne(p,q) == p + 1
    IN FoldSet(PlusOne, 0, D)
```

In the definition of `CardDomain`, we annotated the let-definition `D` with its type, though any type checker should be
able to compute the type of
`D` from its context. So the type of `D` is there for clarification. According to our type grammar, the type of `D` should be `() => Set(a)`, as `D` is an operator. It is not obvious from the syntax: TLA+ blends in nullary operators with other names. We have found that LET-definitions without arguments are so common, so it is more convenient to write the shorter type annotation, that is, just `Set(a)`.

### 2.3. Dealing with bound variables

A number of TLA+ operators are defining bound variables. Following [TLA+
Summary](https://lamport.azurewebsites.net/tla/summary.pdf), we list these
operators here (we omit the unbounded quantifiers and temporal quantifiers):

 * `\A x \in S: P`
 * `\E x \in S: P`
 * `CHOOSE x: P`
 * `{x \in S: P}`
 * `{e: x \in S}`
 * `[x \in S |-> e}`

We do not introduce any special annotation to support these operators. Indeed, they are all introducing bound variables
that range over sets. In most cases, the type checker should be able to extract the element type from a set expression.

However, there are a few pathological cases arising from empty collections. For example:

```tla
/\ \E x \in {}: x > 1
/\ f = [x \in {} |-> 2]
/\ z \in DOMAIN << >>
```

Similar typing issues occur in programming languages, e.g., Scala and Java. In these rare cases, you can write an
auxiliary LET-definition to specify the type of the empty collection:

```tla
/\ LET \* @type: Set(Int);
       EmptyInts == {}
   IN
   \E x \in EmptyInts: x > 1
/\ LET \* @type: Set(Str);
       EmptyStrings == {}
   IN
   f = [x \in EmptyStrings |-> 2]
/\ LET \* @type: Seq(Int);
       EmptyIntSeq == {}
   IN
   z \in DOMAIN EmptyIntSeq
```

The type checker uses the type annotation to refine the type of an empty set
(or, of an empty sequence).

<a id="useTypeAlias"></a>
### 2.4. Introducing and using type aliases

A type alias is introduced with the annotation `@typeAlias: <ALIAS> = <Type>;` 
on a dummy operator called `<PREFIX>TypeAliases`. For example:

```tla
\* @typeAlias: ENTRY = [a: Int, b: Bool];
EXTypeAliases = TRUE

VARIABLE
    \* @type: Set(ENTRY);
    msgs

\* @type: (Set(ENTRY), ENTRY) => ENTRY;
Foo(ms, m) ==
    msgs' = ms \union {m}
```

The use of the dummy operator is a convention followed to simplify reasoning
about where type aliases belong, and to ensure all aliases are located in one
place. The `<PREFIX>` convention protects against name clashes when the  module
is extended or instantiated.

The actual rules around the placement of the `@typeAlias` annotation allows more
flexibility:

1. You can define a type alias with `@typeAlias` anywhere you can define a `@type`.

1. The names of type aliases must be unique in a module.

1. There is no scoping for aliases within a module. Even if an alias is defined
   deep in a tree of LET-IN definitions, it can be references at any level in
   the module.

## 3. Example

As an example that contains non-trivial type information, we chose the specification
of [Cigarette Smokers](https://github.com/tlaplus/Examples/blob/master/specifications/CigaretteSmokers/CigaretteSmokers.tla)
by @mryndzionek from [TLA+ Examples](https://github.com/tlaplus/Examples/tree/master/specifications). In this document,
we focus on the type information and give a shorter version of the specification. For detailed comments,
check [the original
specification](https://github.com/tlaplus/Examples/blob/master/specifications/CigaretteSmokers/CigaretteSmokers.tla).

```tla
---------------------- MODULE CigaretteSmokersTyped --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(*                                                                         *)
(* This specification has been extended with type annotations for the      *)
(* demonstration purposes. Some parts of the original specification are    *)
(* omitted for brevity.                                                    *)
(*                                                                         *)
(* The original specification by @mryndzionek can be found here:           *)
(* https://github.com/tlaplus/Examples/blob/master/specifications/CigaretteSmokers/CigaretteSmokers.tla *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANT
  \* @type: Set(INGREDIENT);
  Ingredients,
  \* @type: Set(Set(INGREDIENT));
  Offers

VARIABLE
  \* @type: INGREDIENT -> [smoking: Bool];
  smokers,
  \* @type: Set(INGREDIENT);
  dealer

(* try to guess the types in the code below *)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

\* @type: (Set(INGREDIENT), (INGREDIENT) => Bool) => INGREDIENT;
ChooseOne(S, P(_)) ==
    (CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x)

Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                    [smoking |-> {r} \union dealer = Ingredients]]
    /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
        (* the type of LAMBDA should be inferred from the types
           of ChooseOne and Ingredients *)
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next ==
    startSmoking \/ stopSmoking

Spec ==
    Init /\ [][Next]_vars

FairSpec ==
    Spec /\ WF_vars(Next)

AtMostOne ==
    Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
=============================================================================
```

[Snowcat tutorial]: https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html
[Snowcat HOWTO]: https://apalache.informal.systems/docs/HOWTOs/howto-write-type-annotations.html
[ADR014]: https://github.com/informalsystems/apalache/blob/unstable/docs/src/adr/014adr-precise-records.md
[Issue 401]: https://github.com/informalsystems/apalache/issues/401

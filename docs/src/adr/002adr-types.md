# ADR-002: types and type annotations

| authors                                | revision |
| -------------------------------------- | --------:|
| Shon Feder, Igor Konnov, Jure Kukovec  |        2 | 

This is a follow up of
[RFC-001](https://github.com/informalsystems/apalache/blob/unstable/docs/internal/rfc/001rfc-types.md), which discusses
plenty of alternative solutions. In this __ADR-002__, we fix one solution that seems to be most suitable. The
interchange format for the type inference tools will be discussed in a separate ADR.

1. How to write types in TLA+ (Type System 1).
1. How to write type annotations (as a user).

This document assumes that one can write a simple type checker that computes the types of all expressions based on the
annotations provided by the user. Our work-in-progress type checker is using these type annotations. The new type
checker can be called with `apalache typecheck` command. Note that the new type checker has not been integrated with the
model checker yet.

In contrast, the [type inference algorithm](https://github.com/informalsystems/apalache/tree/types) by @Kukovec is fully
automatic and thus it eliminates the need for type annotations.
(Jure's algorithm is using Type System 1 too.) However, system engineers often want to write type annotations and
quickly check types when writing TLA+ specifications. This document is filling this gap.

## 1. How to write types in TLA+

### 1.1. Type grammar (Type System 1, or TS1)

We simply write types as strings that follow the type grammar:

```
T ::= typeConst | typeVar | Bool | Int | Str | T -> T | Set(T) | Seq(T) |
      <<T, ..., T>> | [h_1: T, ..., h_k: T] | (T, ..., T) => T | (T)
typeConst ::= <an identifier that matches [A-Z_][A-Z0-9_]*>
typeVar ::= <a single letter from [a-z]>
```      

In this grammar, `h_1`,...,`h_k` are field names. The rule `T -> T` defines a
function, while the rule `(T, ..., T) => T` defines an operator.  Importantly, a
multi-argument function always receives a tuple, e.g., `<<Int, Bool>> -> Int`,
whereas a single-argument function receives the type of its argument, e.g., `Int
-> Int`.  An operator always has the types of its arguments inside `(...)`,
e.g., `(Int, Bool) => Int` and `() => Bool`. The arrow `->` is right-associative,
e.g., `A -> B -> C` is understood as `A -> (B -> C)`, which is consistent with
programming languages. If you like to change the priority of `->`, use parentheses, as usual.
For example, you may write `(A -> B) -> C`. 

If a type `T` contains a type variable, e.g., `a`, then `T` is a
polymorphic type, in which `a` can be instantiated with a monotype (a
variable-free term). Type variables are useful for describing the types of
polymorphic operators. A type constant should be understood as a type we don't
know and we don't want to know, that is, an uninterpreted type. Type constants
are useful for fixing the types of CONSTANTS and using them later in a
specification. Two different type constants correspond to two different -- yet
uninterpreted -- types. If you know [Microsoft
Z3](https://github.com/Z3Prover/z3), a type constant can be understood as an
uninterpreted sort in SMT. Essentially, values of an uninterpreted type can
be only checked for equality.

Assume that notation `e <: T` means that an expression `e` has type `T`.
(More precisely, `T` is a supertype of the type of `e`.)
The following examples demonstrate the use of the type grammar:

* `x` is an integer: `x <: "Int"`.
* `f` is a function from an integer to an integer: `f <: "Int -> Int"`.
* `f` is a function from a set of integers to a set of integers:
    `f <: "Set(Int) -> Set(Int)"`.
* `r` is a record that has the fields `a` and `b`, where `a` is an integer
    and `b` is a string: `r <: "[a: Int, b: Str]"`.
* `F` is a set of functions from a tuple of integers to an integer:
    `F <: "Set(<<Int, Int>> -> Int)"`.
* `Foo` is an operator of an integer and of a string that returns an integer:
    `Foo <: "(Int, Str) => Int"`.
* `Bar` is a higher-order operator that takes an operator that takes
    an integer and a string and returns an integer, and returns a Boolean:
    `Bar <: "((Int, Str) => Int) => Bool"`.
* `Baz` is a polymorphic operator that takes two arguments of the same type
    and returns a value of the type equal to the types of its arguments:
    `Baz <: "(a, a) => a"`.
* `Proc` and `Faulty` are sets of the same type:
    `Proc <: "Set(PID)"` and `Faulty <: "Set(PID)"`.

### 1.2. Discussion    

Our type grammar presents a minimal type system that, in our understanding,
captures all interesting cases that occur in practice. Obviously, this type
system considers ill-typed some perfectly legal TLA+ values. For instance, we
cannot assign a reasonable type to `{1, TRUE}`. However, we can assign a
reasonable type to `{[type |-> "1a", bal |-> 1], [type |-> "2a", bal |-> 2, val
|-> 3]}`, a pattern that often occurs in practice, e.g., see
[Paxos](https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla).
The type of that set will be `Set([type: Str, bal: Int, val: Int])`, which is
probably not what you expected, but it is the best type we can actually compute
without having algebraic datatypes in TLA+. It also reminds the user that one
better tests the field `type` carefully.

Type System 1 is also very much in line with the [type system by Stephan Merz and Hernan Vanzetto](https://dblp.org/search?q=Automatic+Verification+of+%7BTLA%7D+%2B+Proof+Obligations+with+%7BSMT%7D+Solvers)
, which is used internally by
[TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) when translating proof obligations in SMT. We introduce
types for user-defined operators, on top of their types for TLA+ expressions that do not contain user-defined operators.

We expect that this type system will evolve in the future. That is why we call it __Type System 1__. Feel free to
suggest __Type System 2__ :-)

**Note:** For the above example of a set of records, we are considering to introduce union types. So the type of the set

```tla
{[type |-> "1a", bal |-> 1],
 [type |-> "2a", bal |-> 2, val |-> 3]}
```

would be something like:

```tla
Set([type |-> "1a"], bal |-> 1]
  + [type |-> "2a", bal |-> 2, val |-> 3])
```

The value of the field `type` would serve as a type tag. However, we would have to fix a set of patterns that turn a
union type into a precise record type. One such pattern is a set comprehension, e.g., `{ r \in S: r.type = "1a" }`. If
you have ideas, please let us know.

## 2. How to write type annotations (as a user)

We define the Apalache module `Typing.tla` that contains definitions of two operators:

```tla
---- MODULE Typing ----
AssumeType(ex, tp) == TRUE
tp ## ex == ex
=======================
```

The operator `AssumeType(ex, tp)` is a type assumption. It states that `ex`
should have the type whose supertype is `tp` (the records in `tp` may contain
additional fields).  This operator always returns `TRUE`.  The operator `tp ##
ex` annotates an expression `ex` with a type `tp`. This operator returns `ex`
itself, that is, it performs type erasure (for compatibility with other TLA+
tools).

In the following, we discuss how to annotate different TLA+ names.  The
operator `AssumeType` is designated for annotating constants and state
variables, whereas the operator `##` is designated for annotating user-defined
operators.

### 2.1. Annotating CONSTANTS and VARIABLES

Ideally, we would like to use `ASSUME(...)` to annotate the types of state
variables and constants. However, `ASSUME` only allows for constant
expressions.  Hence, we require the annotations of variables and constants to
be defined once per specification with an operator called `TypeAssumptions`.
See the following example:

```tla
EXTENDS Typing
CONSTANT N, Base
VARIABLE x, S

TypeAssumptions ==
  /\ AssumeType(N, "Int")
  /\ AssumeType(Base, "Set(ID)")
  /\ AssumeType(x, "ID")
  /\ AssumeType(S, "Set(ID)")
```

`TypeAssumptions` must be a conjunction of expressions of the form
`AssumeType(nm, tp)`, where `nm` is the name of a VARIABLE or a CONSTANT, and
`tp` is a string in the grammar TS1. No other syntactic forms are allowed.

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

### 2.2. Annotating Operators

The operators in TLA+ are not values, but are similar to macros. Hence, we
cannot refer to an operator by its name, without applying this operator.  To
annotate an operator, we prepend its body with `##` (as proposed by
@shonfeder). For example:

```tla
Mem(e, es) == "(a, Seq(a)) => Bool" ##
    (e \in {es[i]: i \in DOMAIN es})
```

Higher-order operators are also easy to annotate:

```tla
Find(Pred(_), es) == "((a) => Bool, Seq(a)) => Int" ##
    IF \E i \in DOMAIN es: Pred(es[i])
    THEN CHOOSE i \in DOMAIN es: Pred(es[i])
    ELSE -1
```    

The following definition declares a (global) recursive function, not an
operator. However, the annotation syntax is quite similar to that of the
operators (note though that we are using `->` instead of `=>`):

```tla
Card[S \in T] == "Set(a) -> Int" ##
    IF S = {}
    THEN 0
    ELSE LET one_elem == "() => a" ##
            (CHOOSE x \in S: TRUE)
         IN
         1 + Card[S \ {one_elem}]
```

In the definition of `Card`, we annotated the let-definition
`one_elem` with its type, though any type checker should be able to compute
the type of `one_elem` from its context. So the type of `one_elem` is there for
clarification. Note that `one_elem` has the type `() => Int`, as `LET-IN`
defines an operator. Although TLA+ blends in nullary operators with other names,
we feel that it is important to keep this distinction, since we go for a typing
discipline.


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

We do not introduce any special annotation to support these operators.
Indeed, they are all introducing bound variables that range over sets.
In most cases, a type checker should be able to extract the element type
from a set expression.


However, there are a few pathological cases arising from empty collections. For
example:

```tla
/\ \E x \in {}: x > 1
/\ f = [x \in {} |-> 2]
/\ z \in DOMAIN << >>
```

In these rare cases, use the auxiliary operators in the module `Typing` for
specifying the type of the empty collection:

```tla
EXTENDS Typing
...

/\ \E x \in EmptySet("Int"): x > 1
/\ f = [x \in EmptySet("Str") |-> 2]
/\ z \in DOMAIN EmptySeq("Int")
```

The type checker uses the type annotation to refine the type of an empty set
(or, of an empty sequence). To keep compatibility with TLC and other tools,
the module `Typing` defines the operators `EmptySet(...)` and `EmptySeq(...)`
as `{}` and `<<>>`, respectively. However, the type checker overrides these
definitions with the refined types.

## 3. Example

As an example that contains non-trivial type information, we chose the
specification of [Cigarette
Smokers](https://github.com/tlaplus/Examples/blob/master/specifications/CigaretteSmokers/CigaretteSmokers.tla)
by @mryndzionek from [TLA+
Examples](https://github.com/tlaplus/Examples/tree/master/specifications).  In
this document, we focus on the type information and give a shorter version of
the specification. For detailed comments, check [the original
specification](https://github.com/tlaplus/Examples/blob/master/specifications/CigaretteSmokers/CigaretteSmokers.tla).

```tla
-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(*                                                                         *)
(* This specification has been extended with type annotations for the      *)
(* demonstration purposes. Some parts of the original specification are    *)
(* omitted for brevity.                                                    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

EXTENDS Typing \* using the Apalache module for types

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* try to guess the types in the code below *)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

(* are not TypeAssumptions easier? *)
TypeAssumptions ==
    /\ AssumeType(Ingredients, "Set(INGREDIENT)")
    /\ AssumeType(Offers, "Set(Set(INGREDIENT))")
    /\ AssumeType(smokers, "INGREDIENT -> [smoking: Bool]")
    /\ AssumeType(dealer, "Set(INGREDIENT)")

(* this operator has a parametric signature *)
ChooseOne(S, P(_)) == "(Set(a), (a) => Bool) => a" ##
    CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* the types of the actions are fairly obvious *)

Init == "() => Bool" ##
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

startSmoking == "() => Bool" ##
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                    [smoking |-> {r} \cup dealer = Ingredients]]
    /\ dealer' = {}

stopSmoking == "() => Bool" ##
    /\ dealer = {}
        (* the type of LAMBDA should be inferred from the types
           of ChooseOne and Ingredients *)
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN smokers' = [smokers EXCEPT ![r].smoking = FALSE] 
    /\ dealer' \in Offers

Next == "() => Bool" ##
    startSmoking \/ stopSmoking

Spec == "() => Bool" ##
    Init /\ [][Next]_vars

FairSpec == "() => Bool" ##
    Spec /\ WF_vars(Next)    

AtMostOne == "() => Bool" ##
    Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
```

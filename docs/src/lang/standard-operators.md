# The standard operators of TLA+

In this document, we summarize the standard TLA+ operators in a form that is
similar to manuals on programming languages. The purpose of this document is to
provide you with a quick reference, whenever you are looking at the [Summary of
TLA]. The [TLA+ Video
Course](http://lamport.azurewebsites.net/video/videos.html) by Leslie Lamport
is an excellent starting point, if you are new to TLA+.  For a comprehensive
description and philosophy of the language, check [Specifying Systems] and the
[TLA+ Home Page]. You can find handy extensions of the standard library in
[Community Modules].

We explain the semantics of the operators under the lenses of the [Apalache
model checker].  Traditionally, the emphasis was put on the temporal operators
and action operators, as they build the foundation of TLA. We focus on the "+"
aspect of the language, which provides you with a language for writing a single
step by a state machine.  This part of the language is absolutely necessary for
writing and reading system specifications.  Moreover, we treat equally the
"core" operators of TLA+ and the "library" operators: This distinction is less
important to the language users than to the tool developers.

In this document, we present the semantics of TLA+, as if it was executed on a
computer that is equipped with an additional device that we call an _oracle_.
Most of the TLA+ operators are understood as deterministic operators, so they
can be executed on your computer. A few operators are non-deterministic, so
they require the oracle to resolve non-determinism, see [Control Flow and
Non-determinism]. This is one of the most important features that makes TLA+
distinct from programming languages.  Wherever possible, we complement the
English semantics with code in [Python](https://www.python.org/). Although our
semantics are more restrictive than the denotational semantics in Chapter 16 of
[Specifying Systems], they are very close to the treatment of TLA+ by the model
checkers: [Apalache](https://github.com/informalsystems/apalache) and
[TLC](http://lamport.azurewebsites.net/tla/tools.html). Our relation between
TLA+ operators and Python code bears some resemblance to
[SALT](https://github.com/Viasat/salt) and
[PlusPy](https://github.com/tlaplus/PlusPy).

_Here, we are using the ASCII notation of TLA+, as this is what you
type. We give the nice LaTeX notation in the detailed description.  The
translation table between the LaTeX notation and ASCII can be found in [Summary
of TLA]._

## The "+" Operators in TLA+

### Booleans :traffic_light:

_Good old Booleans_. [Learn more...](./booleans.md)

 - Boolean algebra:
   - [`FALSE`](./booleans.md#const) and [`TRUE`](./booleans.md#const),
   - [`A /\ B`](./booleans.md#and) (also `A \land B`),
   - [`A \/ B`](./booleans.md#or) (also `A \lor B`),
   - [`~A`](./booleans.md#not) (also `\lnot A` and `\neg A`),
   - [`A => B`](./booleans.md#implies),
   - [`A <=> B`](./booleans.md#equiv) (also `A \equiv B`)
 - Boolean set: [`BOOLEAN`](./booleans.md#const)

### Control flow and non-determinism :twisted_rightwards_arrows:

 _Hidden powers of TLA+_. [Learn more...](./control-and-nondeterminism.md)

 - Non-determinism with [`A_1 \/ ... \/ A_n`](./control-and-nondeterminism.md#nondetOr)
 - Non-determinism with [`\E x \in S: P`](./control-and-nondeterminism.md#nondetExists)
 - Non-determinism with [`IF p THEN e_1 ELSE e_2`](./control-and-nondeterminism.md#nondetIte)
 - Non-determinism with [`CASE` and `CASE-OTHER`](./control-and-nondeterminism.md#nondetCase)

### Deterministic conditionals :taxi:

 _You need them less often than you think_. [Learn more...](./conditionals.md)

 - Deterministic [`IF-THEN-ELSE`](./conditionals.md#ite)
 - Deterministic [`CASE`](./conditionals.md#case) and [`CASE-OTHER`](./conditionals.md#caseOther)

### Integers :1234:

_Unbounded integers like in Python._ [Learn more...](./integers.md)

 - Integer algebra:
    - [`-i`](./integers.md#uminus), [`i + k`](./integers.md#plus),
        [`i - k`](./integers.md#minus),
    - [`i * k`](./integers.md#mult),
      [`i \div k`](./integers.md#div), [`i % k`](./integers.md#mod),
      [`i^k`](./integers.md#pow)
 - Integer predicates:
    - [`i < k`](./integers.md#lt), [`i > k`](./integers.md#gt),
    - [`i <= k`](./integers.md#lte) (also `i =< k` and `i \leq k`),
        [`i >= k`](./integers.md#gte) (also `i \geq k`)
 - Integer sets: [`i..k`](./integers.md#range),
    [`Int`](./integers.md#const), [`Nat`](./integers.md#const)

### Strings :abcd:

_String constants_. You learned it!

 - String literals, e.g., `"hello"` and `"TLA+ is awesome"`.
   - In Apalache, the literals have the type `Str`.
 - Set of all finite strings: `STRING`.
   - In Apalache, the set `STRING` has the type `Set(Str)`.

### Sets :sushi:

_Like frozen sets in Python, but cooler_ [Learn more...](./sets.md)

 - Set constructors:
   - Enumeration: [`{ e_1, ..., e_n }`](./sets.md#setEnum)
   - Filter: [`{ x \in S: p }`](./sets.md#filter)
   - Map: [`{ e: x \in S }`](./sets.md#map)
   - Powers: [`SUBSET S`](./sets.md#powerset) and [`UNION S`](./sets.md#fold)
 - Set algebra:
   - Union: [`S \union T`](./sets.md#union) (also `S \cup T`),
   - Intersection: [`S \intersect T`](./sets.md#intersect) (also `S \cap T`),
   - Difference: [`S \ T`](./sets.md#setminus)
 - Set predicates:
    - Membership: [`x \in S`](./sets.md#in) and [`x \notin S`](./sets.md#notin),
    - Subsets: [`S \subset T`](./sets.md#subset),
        [`S \subseteq T`](./sets.md#subseteq),
        [`S \supset T`](./sets.md#supset),
        [`S \supseteq T`](./sets.md#supseteq)
    - Finiteness: [`IsFinite`](./sets.md#finite)
 - Cardinality of a finite set: [`Cardinality`](./sets.md#card)

### Logic :octopus:

_How logicians write loops_. [Learn more...](./logic.md)

 - Equality:
    [`=`](./logic.md#eq) and [`/=`](./logic.md#neq) (also `#`)
 - Bounded quantifiers:
    [`\A x \in S: p`](./logic.md#forallBounded) and [`\E x \in S: p`](./logic.md#existsBounded)
 - Unbounded quantifiers:
    [`\A x: p`](./logic.md#forall) and [`\E x: p`](./logic.md#exists)
 - Choice:
    [`CHOOSE x \in S: p`](./logic.md#chooseBounded) and [`CHOOSE x: p`](./logic.md#choose)

### Functions :chart:

_Like frozen dictionaries in Python, but cooler_. [Learn more...](./functions.md)

 - [Function constructor](./functions.md#funCtor): `[ x \in S |-> e ]`
 - [Set of functions](./functions.md#funSetCtor): `[S -> T]`
 - [Function application](./functions.md#funApp): `f[e]`
 - [Function replacement](./functions.md#except): `[ f EXCEPT ![e_1] = e_2 ]`
 - [Function domain](./functions.md#domain): `DOMAIN f`

### Records :books:

_Records like everywhere else_. [Learn more...](./records.md)

 - [Record constructor](./records.md#recCtor): `[ h_1 |-> e_1, ..., h_n |-> e_n ]`
 - [Set of records](./records.md#recSetCtor): `[ h_1: S_1, ..., h_n: S_n ]`
 - [Access by field name](./records.md#recApp): `e.h`
 - Records are functions. All operators of [functions](./functions.md) are supported.

### Tuples :triangular_ruler:

_Well, tuples_, indexed with 1, 2, 3... [Learn more...](./tuples.md)

  - [Tuple constructor](./tuples.md#tuple): `<< e_1, ..., e_n >>`
  - [Cartesian product](./tuples.md#times): `S_1 \X ... \X S_n` (also `S_1 \times ... \times S_n`)
  - Tuples are functions. All operators of [functions](./functions.md) are supported.

### Sequences :snake:

_Functions that pretend to be lists, indexed with 1, 2, 3,..._

  - Add to end: [`Append(s, e)`](./sequences.md#append)
  - First and rest: [`Head(s)`](./sequences.md#head) and [`Tail(s)`](./sequences.md#tail)
  - Length: [`Len(s)`](./sequences.md#len)
  - Concatenation: [`s \o t`](./sequences.md#concat) (also `s \circ t`)
  - Subsequence: [`SubSeq(s, i, k)`](./sequences.md#subseq)
  - Sequence filter: [`SelectSeq(s, Test)`](./sequences.md#filter)
  - Set of finite sequences over `S`: [`Seq(S)`](./sequences.md#seq)
  - Sequences are functions.
    All operators of [functions](./functions.md) and [tuples](./tuples.md) are supported.

### Bags :handbag:

  - TBD

### Reals :lollipop:

 _Like "reals" in your math classes, not floating point_

 - All operators of `Integers` but interpreted over reals

 - `a / b`, `Real`, `Infinity`

### Naturals :paw_prints:

 _If you are Indiana Jones..._

 - All operators of `Integers` except: unary minus `-a` and `Int`

## The "A" Operators in TLA+

### Action operators :runner:

 _Taking a step_

 - Prime: `e'`
 - Preservation: `UNCHANGED e`
 - Stuttering: `[A]_e` and `<A>_e`
 - Action enablement: `ENABLED A`
 - Sequential composition: `A \cdot B`

## The "TL" Operators in TLA+

### Temporal operators :soon:

 _Talking about computations, finite and infinite_

 - Always: `[]F`
 - Eventually: `<>F`
 - Weak fairness: `WF_e(A)`
 - Strong fairness: `SF_e(A)`
 - Leads-to: `F ~> G`
 - Guarantee: `F -+-> G`
 - Temporal hiding: `\EE x: F`
 - Temporal universal quantification: `\AA x: F`

[Control Flow and Non-determinism]: ./control-and-nondeterminism.md
[Apalache model checker]: https://github.com/informalsystems/apalache
[TLC model checker]: http://lamport.azurewebsites.net/tla/tools.html
[Summary of TLA]: https://lamport.azurewebsites.net/tla/summary.pdf
[TLA+ Home Page]: http://lamport.azurewebsites.net/tla/tla.html
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html
[Community Modules]: https://github.com/tlaplus/CommunityModules
[LearnTla.com]: https://learntla.com
[TLA+ Video Course]: http://lamport.azurewebsites.net/video/videos.html

# The standard operators of TLA+

[Back to top](./README.md)

In this document, we summarize the standard TLA+ operators in a form that is
similar to manuals on programming languages. The purpose of this document is to
provide you with a quick reference, whenever you are looking at the [Summary of
TLA]. For a comprehensive description and philosophy of the language, check
[Specifying Systems] and the [TLA+ Home Page]. You can find handy extensions of
the standard library in [Community Modules].

We explain the semantics of the operators under the lenses of the
[Apalache model checker].  Traditionally, the emphasis was put on the temporal
operators and action operators, as they build the foundation of TLA. We focus
on the "+" aspect of the language, as this part of the language is absolutely
necessary for writing and reading system specifications.  Moreover, we treat
equally the "core" operators of TLA+ and the "library" operators: This
distinction is less important to the language users than to the tool developers.

In this document, we present the semantics of TLA+, as if it was executed on a
computer that is equipped with an additional device that we call an _oracle_.
Most of the TLA+ operators are understood as deterministic operators, so they
can be executed on your computer. A few operators are non-deterministic, so
they require the oracle to resolve non-determinism, see [Control Flow and
Non-determinism]. This is one of the most important features that makes TLA+
distinct from programming languages.  Wherever possible, we complement the
English semantics with code in [Python](https://www.python.org/). Although our
semantics is more restrictive than the denotational semantics in Chapter 16 of
[Specifying Systems], it is very close to the treatment of TLA+ by the model
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
  - `FALSE` and `TRUE`,
  - `A /\ B` (also `A \land B`),
  - `A \/ B` (also `A \lor B`),
  - `~A` (also `\lnot A` and `\neg A`),
  - `A => B`,
  - `A <=> B` (also `A \equiv B`)
 - Boolean set: `BOOLEAN`

### Control flow and non-determinism :twisted_rightwards_arrows:

 _Hidden powers of TLA+_. [Learn more...](./control-and-nondeterminism.md)

 - Non-determinism with `A_1 \/ ... \/ A_n`
 - Non-determinism with `\E x \in S: P`
 - Non-determinism with `IF p THEN e_1 ELSE e_2`
 - Non-determinism with `CASE` and `CASE-OTHER`

### Deterministic conditionals :taxi:

 _You need them less often than you think_. [Learn more...](./conditionals.md)

 - Deterministic `IF-THEN-ELSE`
 - Deterministic `CASE` and `CASE-OTHER`

### Integers :1234:

_Unbounded integers like in Python._ [Learn more...](./integers.md)

 - Integer algebra: `-i`, `i + k`, `i - k`, `i * k`, `i \div k`, `i % k`, `i^k`
 - Integer predicates:
    - `i < k`,
    - `i > k`,
    - `i <= k` (also `i =< k` and `i \leq k`), 
    - `i => k` (also `i >= k` and `i \geq k`)
 - Integer sets: `i..k`, `Int`, `Nat`

### Strings :abcd:

_String constants_. You learned it!

 - String literals, e.g., `"hello"` and `"TLA+ is awesome"`
 - Set of all finite strings: `STRING`

### Sets :sushi:

_Like frozen sets in Python, but cooler_ [Learn more...](./sets.md)

 - Set algebra:
   - `S \union T` (also `S \cup T`),
   - `S \intersect T` (also `S \cap T`),
   - `S \ T`
 - Set predicates:
    - `x \in S` and `x \notin S`,
    - `S \subset T`, `S \subseteq T`, `S \supset T`, `S \supseteq T`
 - Set filter: `{ x \in S: p }`
 - Set map: `{ e: x \in S }`
 - Powers: `SUBSET S` and `UNION S`
 - Finite sets: `Cardinality` and `IsFinite`

### Logic :octopus:

_How logicians write loops_. [Learn more...](./logic.md)

 - Equality:
    `=` and `/=` (also `#`)
 - Bounded quantifiers:
    `\A x \in S: p` and `\E x \in S: p`
 - Unbounded quantifiers:
    `\A x: p` and `\E x: p`
 - Choice:
    `CHOOSE x \in S: p` and `CHOOSE x: p`

### Functions :chart:

_Like frozen dictionaries in Python, but cooler_. [Learn more...](./functions.md)

 - Function constructor: `[ x \in S |-> e ]`
 - Set of functions: `[S -> T]`
 - Function application: `f[e]`
 - Function update: `[ f EXCEPT ![e_1] = e_2 ]`
 - Function domain: `DOMAIN f`

### Records :books:

_Records like everywhere else_. [Learn more...](./records.md)

 - All operators of functions
 - Record constructor: `[ h_1 |-> e_1, ..., h_n |-> e_n ]`
 - Set of records: `[ h_1: S_1, ..., h_n: S_n ]`
 - Access by field name: `e.h`

### Tuples :triangular_ruler:

_Well, tuples_, indexed with 1, 2, 3... [Learn more...](./tuples.md)

  - All operators of functions
  - Tuple constructor: `<< e_1, ..., e_n >>`
  - Cartesian product: `S_1 \X ... \X S_n` (also `S_1 \times ... \times S_n`)

### Sequences :snake:

_Functions that pretend to be lists, indexed with 1, 2, 3,..._

  - All operators of functions and tuples
  - Sequence constructor: `<< e_1, ..., e_n >>` (exactly as tuple)
  - Concatenation: `s \o t` (also `s \circ t`)
  - Add to end: `Append(s, e)`
  - First and rest: `Head(s)` and `Tail(s)`
  - Length: `Len(s)`
  - Subsequence: `SubSeq(s, i, k)`
  - Sequence filter: `SelectSeq(s, Test)`
  - Set of finite sequences over `S`: `Seq(S)`

### Bags :handbag:

  - TBD

### Reals

 _Like "reals" in your math classes, not floating point_

 - All operators of `Integers`

 - `a / b`, `Real`, `Infinity`

### Naturals

 _If you are Indiana Jones..._

 - All operators of `Integers` except: unary minus `-a` and `Int`

## The "A" Operators in TLA+

### Action operators

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
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book
[Community Modules]: https://github.com/tlaplus/CommunityModules
[LearnTla.com]: https://learntla.com


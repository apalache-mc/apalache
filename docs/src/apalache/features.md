Here is the list of the TLA+ language features that are currently supported by Apalache, following the [Summary of TLA+][cheat].

## Safety vs. Liveness

At the moment, Apalache is able to check state invariants, action invariants,
trace invariants as well as inductive invariants. See the [page on
invariants](https://apalache.informal.systems/docs/apalache/invariants.html) in
the manual. Which means that you can only check safety properties with
Apalache, unless you employ a [liveness-to-safety] transformation in your spec.
In general, we do not support checking liveness properties.  If you would like
to see liveness implemented, upvote the [liveness feature].

## Language

### Module-Level constructs

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``EXTENDS module`` | ✔ | - |  A few standard modules are not supported yet (Bags)
``CONSTANTS C1, C2`` | ✔ | -  | Either define a ``ConstInit`` operator to initialize the constants, use a `.cfg` file, or declare operators instead of constants, e.g., C1 == 111
``VARIABLES x, y, z`` | ✔ | - |
``ASSUME P`` | ✔ / ✖ | - | Parsed, but not propagated to the solver
``F(x1, ..., x_n) == exp`` | ✔ / ✖ | - | Every application of `F` is replaced with its body. Recursive operators need [unrolling annotations](./principles.md#recursive-operators). From 0.16.1 and later, for better performance and UX, use `FoldSet` and `FoldSeq`.
``f[x ∈ S] == exp`` | ✔ / ✖ | - | Recursive functions are only supported if they return integers or Booleans. From 0.16.1 and later, for better performance and UX, use `FoldSet` and `FoldSeq`.
``INSTANCE M WITH ...`` | ✔ / ✖ | - | No special treatment for ``~>``, ``\cdot``, ``ENABLED``
``N(x1, ..., x_n) == INSTANCE M WITH...`` | ✔ / ✖ | - | Parameterized instances are not supported
``THEOREM P`` | ✔ / ✖ | - | Parsed but not used
``LOCAL def`` | ✔ | - | Replaced with local LET-IN definitions

### The constant operators

#### Logic

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`/\`, `\/`, `~`, `=>`, `<=>` | ✔ | - |
``TRUE``, ``FALSE``, ``BOOLEAN`` | ✔ | - |
``\A x \in S: p``, ``\E x \in S : p`` |  ✔ | - |
``CHOOSE x \in S : p`` |  ✖ | - | Partial support prior to version 0.16.1. From 0.16.1 and later, use `Some`, `FoldSet`, or `FoldSeq`. See [#841](https://github.com/informalsystems/apalache/issues/841).
``CHOOSE x : x \notin S`` |  ✖ | - | Not supported. You can use records or a default value such as -1.
``\A x : p, \E x : p`` |  ✖ | - | Use bounded quantifiers
``CHOOSE x : p`` |  ✖ | - |


#### Sets

**Note:** only finite sets are supported. Additionally, existential
quantification over `Int` and `Nat` is supported, as soon as it can be
replaced with a constant.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`=`, `/=`, `\in`, `\notin`, `\intersect`, `\union`, `\subseteq`, `\`  | ✔ | - |
`{e_1, ..., e_n}` | ✔ | - |
`{x \in S : p}` | ✔ | - |
`{e : x \in S}` | ✔ | - |
`SUBSET S` | ✔ | - | Sometimes, the powersets are expanded
`UNION S` |  ✔ | - | Provided that S is expanded

#### Functions

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`f[e]` | ✔ | - |
`DOMAIN f` | ✔ | - |
`[ x \in S ↦ e]` | ✔ | - |
`[ S -> T ]` | ✔ | - | Supported, provided the function can be interpreted symbolically
`[ f EXCEPT ![e1] = e2 ]` | ✔ | - |

#### Records

*Use [type
annotations](https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html)
to help the model checker in finding the right types.* Note that our type
system distinguishes records from general functions.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`e.h` | ✔ | - |
`r[e]` | ✔/✖ | - | Provided that `e` is a constant expression.
`[ h1 ↦ e1, ..., h_n ↦ e_n]` | ✔ | - |
`[ h1 : S1, ..., h_n : S_n]` | ✔ | - |
`[ r EXCEPT !.h = e]` | ✔ | - |

#### Tuples

*Use [type
annotations](https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html)
to help the model checker in finding the right types.* Note that our type
system distinguishes records from general functions.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`e[i]` | ✔ / ✖ | - | Provided that `i` is a constant expression
`<< e1, ..., e_n >>` | ✔ | - | Use a [type annotation](https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html) to distinguish between a tuple and a sequence.
`S1 \X ... \X S_n` | ✔ | - |
`[ t EXCEPT ![i] = e]` | ✔/✖ | - | Provided that `i` is a constant expression

#### Strings and numbers

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`"c1...c_n"` | ✔ | - | A string is always mapped to a unique uninterpreted constant
`STRING` | ✖ | - | It is an infinite set. We cannot handle infinite sets.
`d1...d_n` | ✔ | - | As long as the SMT solver (Z3) accepts that large number
`d1...d_n.d_n+1...d_m` | ✖ | - | Technical issue. We will implement it upon a user request.

#### Miscellaneous Constructs

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`IF p THEN e1 ELSE e2` | ✔ | - | Provided that both e1 and e2 have the same type
`CASE p1 -> e1 [] ... [] p_n -> e_n [] OTHER -> e` | ✔ | - | Provided that `e1, ..., e_n, e` have the same type
`CASE p1 -> e1 [] ... [] p_n -> e_n` | ✔ | - | Provided that `e1, ..., e_n` have the same type
`LET d1 == e1 ... d_n == e_n IN e` | ✔ |  | All applications of `d1`, ..., `d_n` are replaced with the expressions `e1`, ... `e_n` respectively. LET-definitions without arguments are kept in place.
multi-line `/\` and `\/` | ✔ | - |

### The Action Operators

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`e'` | ✔ | - |
`[A]_e` | ✖ | - | It does not matter for safety
`< A >_e` | ✖ | - |
`ENABLED A` | ✖ | - |
`UNCHANGED <<e_1, ..., e_k>>` | ✔ | - |Always replaced with `e_1' = e_1 /\ ... /\ e_k' = e_k`
`A ∙ B` | ✖ | - |

### The Temporal Operators

The model checker assumes that the specification has the form `Init /\
[][Next]_e`. Given an invariant candidate `Inv`, the tool checks, whether
`Inv` is violated by an execution whose length is bounded by the given
argument.

Except the standard form `Init /\ [][Next]_e`, no temporal operators are supported.

## Standard modules

### Integers and Naturals

For the moment, the model checker does not differentiate between integers and naturals. They are all translated as integers in SMT.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`+`, `-`, `*`, `<=`, `>=`, `<`, `>` | ✔ | - | These operators are translated into integer arithmetic of the SMT solver. Linear integer arithmetic is preferred.
`\div`, `%` | ✔ | - | Integer division and modulo
`a^b` | ✔ / ✖ | - | Provided a and b are constant expressions
`a..b` | ✔ / ✖ | - | Sometimes, `a..b` needs a constant upper bound on the range.  When Apalache complains, use `{x \in A..B : a <= x /\ x <= b}`, provided that `A` and `B` are constant expressions.
`Int`, `Nat` | ✔ / ✖ | - | Supported in `\E x \in Nat: p` and `\E x \in Int: p`, if the expression is not located under `\A` and `~`. We also support assignments like `f' \in [S -> Int]` and tests `f \in [S -> Nat]`
`/` | ✖ | - | Real division, not supported

### Sequences

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``<<...>>``, ``Head``, ``Tail``, ``Len``, ``SubSeq``, `Append`, `\o`, `f[e]` | ✔ | - | The sequence constructor ``<<...>>`` needs a [type annotation](https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html).
`EXCEPT` | ✖ |   | If you need it, let us know, issue #324
`Seq(S)` | ✖ | - | Use `Gen` of Apalache to produce bounded sequences
`SelectSeq` | ✖ | - | Planned in [#873](https://github.com/informalsystems/apalache/issues/873). Till then, use `FoldSeq`.

### FiniteSets

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``IsFinite`` | ✔ | - | Always returns true, as all the supported sets are finite
``Cardinality`` | ✔ | - | Try to avoid it, as `Cardinality(S)` produces `O(n^2)` constraints in SMT for cardinality `n`

### TLC

Operator   | Supported?         | Milestone       | Comment
-----------|:------------------:|:---------------:|--------------
`a :> b`   | ✔                  | -               | A singleton function `<<a, b>>`
`f @@ g`   | ✔                  | -               | Extends function `f` with the domain and values of function `g`
Other operators |               |                 | Dummy definitions for spec compatibility

### Reals

Not supported, not a priority




[cheat]: https://lamport.azurewebsites.net/tla/summary.pdf
[liveness-to-safety]: https://www.sciencedirect.com/science/article/pii/S1571066104804109?via%3Dihub
[liveness feature]: https://github.com/informalsystems/apalache/issues/488

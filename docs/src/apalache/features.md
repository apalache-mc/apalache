Here is the list of the TLA+ language features that are currently supported by Apalache, following the [Summary of TLA+][cheat].

## Safety vs. Liveness

At the moment, Apalache is able to check invariants and inductive invariants.
It means that you can only check safety with Apalache, unless you employ
[liveness-to-safety] transformation in your spec. It does not support
liveness properties.  If you really like to see liveness implemented, upvote
the [liveness feature].

## Language

### Module-Level constructs

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``EXTENDS module`` | ✔ | - | As soon as SANY imports the module. Some standard modules are not supported yet
``CONSTANTS C1, C2`` | ✔ | -  | Either define a ``ConstInit`` operator to initialize the constants, or declare operators instead of constants, e.g., C1 == 111
``VARIABLES x, y, z`` | ✔ | - |
``ASSUME P`` | ✔ / ✖ | - | Parsed, but not propagated to the solver
``F(x1, ..., x_n) == exp`` | ✔ / ✖ | - | Every application of `F` is replaced with its body. Recursive operators need [unrolling annotations](./principles.md#recursive-operators).
``f[x ∈ S] == exp`` | ✔ / ✖ | - | Only recursive functions that return integers or Booleans are supported.
``INSTANCE M WITH ...`` | ✔ / ✖ | - | No special treatment for ``~>``, ``\cdot``, ``ENABLED``
``N(x1, ..., x_n) == INSTANCE M WITH...`` | ✔ / ✖ | - | Parameterized instances are not supported yet, LOCAL operator definitions inside instances may fail to work
``THEOREM P`` | ✔ / ✖ | - | Parsed but not used
``LOCAL def`` | ✔ | - | Handled by SANY

### The constant operators

#### Logic

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`/\`, `\/`, `~`, `=>`, `<=>` | ✔ | - |
``TRUE``, ``FALSE``, ``BOOLEAN`` | ✔ | - |
``\A x \in S: p``, ``\E x \in S : p`` |  ✔ | - |
``CHOOSE x \in S : p`` |  ✔/✖ | - | Similar to TLC, we implement a non-deterministic choice. We will add a deterministic version in the future.
``CHOOSE x : x \notin S`` |  ✖ | ? | That is a commonly used idiom
``\A x : p, \E x : p`` |  ✖ | **NEVER** | Use the versions above
``CHOOSE x : p`` |  ✖ | **NEVER** | Use the version above


#### Sets

**Note:** only finite sets are supported. Additionally, existential
quantification over `Int` and `Nat` is supported, as soon as it can be
replaced with a constant.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`=`, `/=`, `\in`, `\notin`, `\intersect`, `\union`, `\subseteq`, `\`  | ✔ | - |
`{e_1, ..., e_n}` | ✔ | - | Empty sets ``{}`` require [type annotations](types-and-annotations.md)
`{x \in S : p}` | ✔ | - |
`{e : x \in S}` | ✔ | - |
`SUBSET S` | ✔ | - | Sometimes, the powersets are expanded
`UNION S` |  ✔ | - | Provided that S is expanded

#### Functions

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`f[e]` | ✔ | - |
`DOMAIN f` | ✔ | - |
`[ x \in S ↦ e]` | ✔ / ✖ | - |  
`[ S -> T ]` | ✔ | - | Sometimes, the functions sets are expanded
`[ f EXCEPT ![e1] = e2 ]` | ✔ | - |

#### Records

*Use [type annotations](types-and-annotations.md) to help the model checker in finding the right types.*
Note that our type system distinguishes records from general functions.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`e.h` | ✔ | - |
`r[e]` | ✔/✖ | - | Provided that e is a constant expression.
`[ h1 ↦ e1, ..., h_n ↦ e_n]` | ✔ | - |
`[ h1 : S1, ..., h_n : S_n]` | ✔ | - |
`[ r EXCEPT !.h = e]` | ✔ | - |

#### Tuples

*Use [type annotations](types-and-annotations.md) to help the model checker in finding the right types.*
Note that our type system distinguishes tuples from general functions.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`e[i]` | ✔ / ✖ | - | Provided that ``i`` is a constant expression
`<< e1, ..., e_n >>` | ✔ | - | By default, a tuple is constructed. Use a [type annotation](types-and-annotations.md) to construct a sequence of proper type.
`S1 \X ... \X S_n` | ✔ | - |
`[ t EXCEPT ![i] = e]` | ✔/✖ | - | Provided that ``i`` is a constant expression

#### Strings and numbers

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`"c1...c_n"` | ✔ | - | A string is always mapped to a unique uninterpreted constant
`STRING` | ✖ | - | It is an infinite set. We cannot handle infinite sets.
`d1...d_n` | ✔ | - | As long as the SMT solver (Z3) accepts that large number
`d1...d_n.d_n+1...d_m` | ✖ | - | Technical issue. We will implemented upon a user request.

#### Miscellaneous Constructs

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
`IF p THEN e1 ELSE e2` | ✔ | - | Provided that both e1 and e2 have the same type
`CASE p1 -> e1 [] ... [] p_n -> e_n [] OTHER -> e` | ✔ | - | See the comment above
`CASE p1 -> e1 [] ... [] p_n -> e_n` | ✖ | - | Introduce the default arm with `OTHER`.
``LET d1 == e1 ... d_n == e_n IN e`` | ✔ / ✖ | `0.7-dev-calls` | All applications of `d1`, ..., `d_n` are replaced with the expressions `e1`, ... `e_n` respectively. LET-definitions without arguments are kept in place.
multi-line `/\` and `\/` | ✔ | - |

### The Action Operators

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``e'`` | ✔ / ✖ | - | Provided that e is a variable
``[A]_e`` | ✖ | - | It does not matter for safety
``< A >_e`` | ✖ | - |
``ENABLED A`` | ✖ | - |
``UNCHANGED <<e_1, ..., e_k>>`` | ✔ | - |	Always replaced with ``e_1' = e_1 /\ ... /\ e_k' = e_k``
``A ∙ B`` | ✖ | - |

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
``<<...>>``, ``Head``, ``Tail``, ``Len``, ``SubSeq``, `Append`, `\o`, `f[e]` | ✔ | - | The sequence constructor ``<<...>>`` needs a [type annotation](types-and-annotations.md).
``EXCEPT`` | ✖ | `0.9` | this operator do not seem to be often used
``Seq(S)`` | ✖ | - | We need an upper bound on the length of the sequences.
``SelectSeq`` | ✖ | - | will not be supported in the near future

### FiniteSets

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``IsFinite`` | ✔ | - | Always returns true, as all the supported sets are finite
``Cardinality`` | ✔ | - | Try to avoid it, as Cardinality(S) produces ``O(n^2)`` constraints in SMT for cardinality `n`

### TLC

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
``f @@ a :> b`` | ✔ | - | Extends the function relation with the pair ``<<a, b>>``

### Reals

Not supported, not a priority




[cheat]: https://lamport.azurewebsites.net/tla/summary.pdf
[liveness-to-safety]: https://www.sciencedirect.com/science/article/pii/S1571066104804109?via%3Dihub
[liveness feature]: https://github.com/informalsystems/apalache/issues/488


# ADR-020: Introduce static membership in arenas

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Igor Konnov                            | 2022-06-01      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

We discuss an extension of the model checker arenas. The main application of this extension is a more efficient
implementation of powersets and functions sets. Potentially, this extension will let us optimize the number of SMT
constraints and thus improve performance of the model checker in general.

## 1. Context

We give only a brief introduction to arenas. A detailed exposition can be found in [KKT19][].

### 1.1. Short introduction to arenas

The model checker heavily relies on the concept of arenas, which are a static overapproximation of the data structures
produced by symbolic execution of a TLA+ specification. Here we give a very short recap. In a nutshell, all basic values
of TLA+ (such as integers, strings, and Booleans) and data structures
(sets, functions, records, tuples, and sequences) are translated into *cells*. Cells are SMT constants, which can be
connected to other cells by *edges*. Currently, we have three kinds of edges:

- **has**. A membership edge `(c_p, c_e)` represents that a parent cell `c_p`
  potentially contains an element `c_e` (e.g., if `c_p` represents a set). These edges encode many-to-many relations.

- **dom**. A domain edge `(c_f, c_d)` represents that a function cell `c_f`
  has the domain represented with a cell `c_d`. These edges encode many-to-one relations.

  Likewise, a domain edge `(c_F, c_c)` represents that a function set cell
  `c_F` has the domain represented with a cell `c_c`.

- **cdm**. A co-domain edge `(c_F, c_c)` represents that a function set cell
  `c_F` has the co-domain represented with a cell `c_c`. These edges encode many-to-one relations.

  For historic reasons, functions are also encoded with the edges called
  **dom** and **cdm**, though the **cdm** edge points to the function relation, not its co-domain. We would prefer to
  call label the relation edge with **rel**, not **cdm**. As these edges are many-to-one, we can map them from their
  kinds `kind -> (c_p, c_e)`. This requires simple refactoring, so we are not going to discuss the **dom** and **cdm**
  any further.

There is a need for refactoring and extension of the **has**-edges. We
summarize the issues with the current implementation of this kind of edges:

- Originally, every edge `(c_S, c_e)` of the kind **has** was encoded as a Boolean constant `in_${c_e.id}_${c_S.id}` in
  SMT. Hence, every time we introduce a copy `c_T` of a set `c_S`, we introduce a new edge
  `(c_T, c_e)` in the arena, and thus we have to introduce another Boolean constant `in_${c_e.id}_${c_T.id}` in SMT.
  Alternatively, we could use a single Boolean variable both for `(c_S, c_e)` and `(c_T, c_e)`.

- Later, when translating records and tuples, we stopped introducing Boolean constants in SMT for the **has**-edges.
  However, we do not track in the arena the fact that these edges are presented only in the arena, not in SMT. Hence, we
  have to be careful and avoid expressing membership in SMT when working with these edges.

- As every **has**-edge directly refers to its parent in the edge name (that is, `in_${c_e.id}_${c_S.id}`), we cannot
  share edges when encoding `SUBSET S` and `[S -> T]`. As a result, we have to introduce a massive number of Boolean
  constants and constraints, which are not necessary.

- We keep adding edges and SMT constants to the solver context, even when we know exactly that an element belongs to a
  set, e.g., as in `{ 1, 2, 3 }`.

### 1.2. Arena examples

To introduce the context in more detail, we give an example of how several TLA+ expressions are represented in arenas
and SMT.

Consider the following expression:

```tla
{ a, b, c } \union { d, e }
```

Let's denote the arguments of the set union to be `S` and `T`. In the current arena representation, the rewriting
rule `SetCtorRule` creates the following SMT constants (assuming that `a, ..., e` were translated to arena cells):

- Two cells `c_l` and `c_r` to represent the sets `S` and `T`. These cells are backed with two SMT constants of an
  uninterpreted sort, which corresponds to the common type of `S` and `T`.

- Five SMT constants of the Boolean sort that express set membership of `a, b, c` and `d, e` in `S` and `T`,
  respectively. The sets `S` and `T` are backed with SMT constants of the sort of `S` and `T`.

- One cell `c_u` to represent the set `S \union T`.

- Five Boolean constants of the Boolean sort that express set membership of
  `a, b, c, d, e` in `S \union T`.

It is obvious that 10 Boolean constants introduced for set membership are completely unnecessary, as we know for sure
that the respective elements belong to the three sets. Moreover, when constructing `S \union T`, the rule `SetCupRule`
creates five SMT constraints:

```smt
;; a, b, c belong to the union, when they belong to S
(= in_a_u in_a_l)
(= in_b_u in_b_l)
(= in_c_u in_c_l)
;; d and e belong to the union, when they belong to T
(= in_d_u in_d_r)
(= in_e_u in_e_r)
```

## 2. Options

- Keep things as they are.

- Implement the extension of membership edges presented below.

## 3. Solution

### 3.1. Pointers to the elements

Instead of the current solution in the arenas, which maps a parent cell to a
list of element cells, we propose to map parent cells to membership pointers of
various kinds. To this end, we introduce an abstract edge (the Scala code can
be found in the package `at.forsyte.apalache.tla.bmcmt.arena`):


https://github.com/informalsystems/apalache/blob/81e397fadc6f3ce346d8f8a709ebb3715ac57391/tla-bmcmt/src/main/scala/at/forsyte/apalache/tla/bmcmt/arena/ElemPtr.scala#L8-L24

Having an abstract edge, we introduce various case classes. The simplest case
is the `FixedElemPtr`, which always evaluates to a fixed Boolean value:

https://github.com/informalsystems/apalache/blob/81e397fadc6f3ce346d8f8a709ebb3715ac57391/tla-bmcmt/src/main/scala/at/forsyte/apalache/tla/bmcmt/arena/ElemPtr.scala#L26-L39

Instances of `FixedElemPtr` may be used in cases, when the membership is
statically known. For instance, set membership for the sets `{1, 2, 3}` and
`1..100` is static (always `true`) and thus it does not require any additional
variables and constraints in SMT. The same applies to records and tuples.

The next case is element membership that is represented via a Boolean constant
in SMT:

https://github.com/informalsystems/apalache/blob/81e397fadc6f3ce346d8f8a709ebb3715ac57391/tla-bmcmt/src/main/scala/at/forsyte/apalache/tla/bmcmt/arena/ElemPtr.scala#L41-L64

Instances of `SmtConstElemPtr` may be used in cases, when set membership can be
encoded via a Boolean constant. Typically, this is needed when the membership
is either to be defined by the solver, or when this constant caches a complex
SMT constraint. For instance, it can be used by `CherryPick`.

The most general case is represented via an SMT expression, which is encoded in
TLA+ IR:

https://github.com/informalsystems/apalache/blob/81e397fadc6f3ce346d8f8a709ebb3715ac57391/tla-bmcmt/src/main/scala/at/forsyte/apalache/tla/bmcmt/arena/ElemPtr.scala#L66-L77

Instances of `SmtExprElemPtr` may be used to encode set membership via SMT
expressions. For instance:

 - Evaluating an array expression, e.g., via `apalacheStoreInFun`.

 - Combining several pointers. For instance, when computing `{ x \in S: P }`,
   we would combine set membership in `S` and the value of `P` for every `x`.

### 3.2. Optimization 1: constant propagation via membership pointers

One immediate application of using the new representation is completely SMT-free construction of some of the TLA+
expressions.

Recall the example in [Section 1.2](#12-arena-examples). With the new representation, the set constructor would simply
create five instances of
`FixedElemPtr` that carry the value `true`, that is, the elements unconditionally belong to `S` and `T`. Further, the
rule `SetCupRule` would simply copy the five pointers, without propagating anything to SMT.

As a result, we obtain constant propagation of set membership, while keeping the general spirit of the arena-based
encoding.

### 3.3. Optimization 2: sharing membership in a powerset

Consider the TLA+ operator that constructs the powerset of `S`, that is, the set
of all subsets of `S`:

```tla
SUBSET S
```

Let `c_S` be the cell that represents the set `S` and `c_1, ..., c_n` be the
cells that represent the potential elements of `S`. Note that in general,
membership of all these cells may be statically unknown. For example, consider
the case when the set `S` is constructed from the following TLA+ expression:

```tla
{
  x \in 1..100:
    \E y \in 1..10:
      y * y = x
}
```

In the above example, computation of the predicate is delegated to the SMT solver.

The code in `PowSetCtor` constructs `2^Cardinality(S)` sets that contain all subsets of `S`. The tricky part here is
that some of the elements of `S` may be outside of `S`. To deal with that, `PowSetCtor` constructs cells for each
potential combinations of `c_1, ..., c_n` and adds membership tests for each of them. For instance, consider the
subset `T` that is constructed by selecting the indices `1, 3, 5` of `1..n`. The constructor will introduce three
constraints:

```smt
(= in_c_1_T in_c_1_S)
(= in_c_3_T in_c_3_S)
(= in_c_5_T in_c_5_S)
```

Hence, the current encoding introduces `2^n` SMT constants for the subsets and
`n * 2^(n - 1)` membership constraints in SMT (thanks to Jure @Kukovec for
telling me the precise formula).

With the new representation, we would simply copy the respective membership
pointers of the set `S`. This would require us to introduce zero constraints in
the SMT, though we would still introduce `2^n` SMT constants to represent the
subsets themselves. Note that we would still have to introduce `n * 2^(n - 1)`
pointers in the arena. But this would be done during the process of rewriting.

### 3.4. Feature: computing the set of functions via pointer sharing

Sometimes, it happens that the model checker has to expand a set of functions
`[S -> T]`. Such a set contains `|T|^|S|` functions. Since the model checker works with arenas, it can only construct an arena representation of `[S ->
T]`. To this end, assume that the set `S` is encoded via cells `s_1, ..., s_m`,
and the set `T` is encoded via cells `t_1, ..., t_n`.

If we wanted to construct `[S -> T]` in the current encoding, we would have to
introduce a relation for each function in the set `[S -> T]`. That is, for
every sequence `i[1], ..., i[n]` over `1..n`, it would construct the relation
`R`:

    { <<s_1, t_i[1]>>, ..., <<s_m, t_i[m]>> }

Let's denote with `p_j` the pair `<<s_j, t_i[j]>>` for `1 <= j <= m`.

Moreover, we would add `m` membership constraints (per function!) in SMT:

    (= in_p_1_R (and in_s_1_S in_t_i[1]_T))
    ...
    (= in_p_m_R (and in_s_m_S in_t_i[m]_T))

As a result, this encoding would introduce `m * n^m` constants in SMT and the same number of membership constraints. For
instance, if we have `m = 10` and `n = 5`, then we would introduce 90 million constants and constraints!

Using the approach outlined in this ADR, we can simply combine membership pointers of `S` and `T` via `SmtExprElemPtr`.
This would neither introduce SMT constants, nor SMT constraints. Of course, when this set is used in expressions
like `\E x \in S: P` or `\A x \in S: P`, the edges will propagate to SMT as constraints.

## 4. Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

[KKT19]: https://dl.acm.org/doi/10.1145/3360549

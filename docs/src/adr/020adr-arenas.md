---
authors: Igor Konnov
last revised: 2022-05-16
---

# ADR-020: Improving membership in arenas

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

We discuss an extension of membership edges in arenas. The main application of
this extension would be a more efficient implementation of powersets and a
functions sets. Potentially, this extension will let us optimize the number of
SMT constraints and thus improve performance of the model checker in general.

## 1. Context

The model checker heavily relies on the concept of arenas, which are a static
overapproximation of the data structures produced by symbolic execution of a
TLA+ specification. Arenas are explained in detail in [KKT19][]. Here we give a
very short recap. In a nutshell, all basic values of TLA+ (such as integers,
strings, and Booleans) and data structures (sets, functions, records, tuples,
and sequences) are translated into *cells*. Cells are SMT constants, which can
be connected to other cells. Cells are connected with one another by the means
of edges. Currently, we have three kinds of edges:

 - **has**. A membership edge `(c_p, c_e)` represents that a parent cell `c_p`
   potentially contains an element `c_e` (e.g., if `c_p` represents a set).
   These edges encode many-to-many relations.

 - **dom**. A domain edge `(c_f, c_d)` represents that a function cell `c_f`
   has the domain represented with a cell `c_d`.
   These edges encode many-to-one relations.

 - **cdm**. A co-domain edge `(c_F, c_c)` represents that a function set cell
   `c_F` has the co-domain represented with a cell `c_c`.
   These edges encode many-to-one relations.

   *For historic reasons, functions are also encoded with the edges called
   **dom** and **cdm**, though the **cdm** edge points to the function
   relation, not its co-domain. This should be fixed!*

Having the edges of kinds **dom** and **cdm** happened to be two inflexible.
As we explained above, sometimes we would like to have another edge kind called
**rel**. As these edges are many-to-one, we can map them from their kinds `kind
-> (c_p, c_e)`. This requires simple refactoring, so we are not going to
discuss the **dom** and **cdm** any further.

There is a need for refactoring and extension of the **has**-edges. We
summarize the issues with the current implementation of this kind of edges:

 - Originally, every edge `(c_S, c_e)` of the kind **has** was encoded as a
   Boolean constant `in_${c_e.id}_${c_S.id}` in SMT. Hence, every time the edge
   is copied to another set cell `c_T`, we have to introduce another Boolean
   constant `in_${c_e.id}_${c_T.id}` in SMT. As a result, two set cells do not
   share edges. This causes unnecessary duplication of SMT constants and
   constraints.

 - Later, we stopped introducing Boolean constants in SMT for the **has**-edges
   when translating records and tuples. However, we do not record the fact that
   these edges are presented only in the arena, not in SMT. Hence, we have to
   be careful and do not use the SMT membership when working with these edges.

 - As every **has**-edge directly refers to its parent in the edge name (that
   is, `in_${c_e.id}_${c_S.id}`), we cannot share edges when encoding `SUBSET
   S` and `[S -> T]`. As a result, we have to introduce a massive number of
   Boolean constants and constraints, which are not necessary.

 - We keep adding edges and SMT constants to the solver context, even when we
   know exactly that an element belongs to a set, e.g., as in `{ 1, 2, 3 }`.

## 2. Options

 - Keep things as they are.

 - Extend the edges.


## 3. Solution

### 3.1. Pointers to the elements

Instead of the current solution in the arenas, which maps a parent cell to a
list of element cells, we propose to map parent cells to membership pointers of
various kinds. To this end, we introduce an abstract edge (the Scala code can
be found in the package `at.forsyte.apalache.tla.bmcmt.arena`):

```scala
/**
 * An abstract membership pointer.
 */
sealed trait ElemPtr {

  /**
   * Get the element that this edge is pointing to.
   * @return
   *   an arena cell that is pointed by this pointer
   */
  def elem: ArenaCell

  /**
   * Translate the membership test into an expression that can be understood by Z3SolverContext.
   */
  def toSmt: TlaEx
}
```

Having an abstract edge, we introduce various case classes. The simplest case
is the `FixedElemPtr`, which always evaluates to a fixed Boolean value:

```scala
/**
 * An element pointer that always evaluates to a fixed Boolean value.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param value
 *   the value (false or true).
 */
case class FixedElemPtr(elem: ArenaCell, value: Boolean) extends ElemPtr {
  override def toSmt: TlaEx = {
    tla.bool(value).as(BoolT1())
  }
}
```

Instances of `FixedElemPtr` may be used in cases, when the membership is
statically known. For instance, set membership for the sets `{ 1, 2, 3}` and
`1..100` is static (always `true`) and thus it does not require any additional
variables and constraints in SMT. The same applies to records and tuples.

The next case is element membership that is represented via a Boolean constant
in SMT:

```scala
/**
 * An element pointer whose value is encoded as a Boolean constant. Its value is found by the SMT solver.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param id
 *   the unique id of the pointer.
 */
case class SmtConstElemPtr(elem: ArenaCell, id: UID) extends ElemPtr {
  val uniqueName = s"_bool_elem$id"

  override def toSmt: TlaEx = {
    tla.name(uniqueName).as(BoolT1())
  }
}
```

Instances of `SmtConstElemPtr` may be used in cases, when set membership can be
encoded via a Boolean constant. Typically, this is needed when the membership
is either to be defined by the solver, or when this constant caches a complex
SMT constraint. For instance, it can be used when computing a filter expression
`{ x \in S: P }`.

The most general case is represented via an SMT expression, which is encoded in
TLA+ IR:

```scala
/**
 * An element pointer whose value is encoded via an SMT expression.
 * @param elem
 *   the element this pointer is pointing to.
 * @param smtEx
 *   the corresponding SMT expression.
 */
case class SmtExprElemPtr(elem: ArenaCell, smtEx: TlaEx) extends ElemPtr {
  override def toSmt: TlaEx = smtEx
}
```

Instances of `SmtExprElemPtr` may be used to encode set membership via SMT
expressions. For instance:

 - Evaluating an array expression, e.g., via `apalacheStoreInFun`.

 - Perhaps combining several pointers. No concrete example yet.

### 3.2. Optimization 1: constant propagation via membership pointers

One immediate application of using the new representation is completely
SMT-free construction of some of the TLA+ expressions. Consider the following
expression:

```tla
{ a, b, c } \union { d, e }
```

Let's denote the arguments of the set union to be `S` and `T`. In the current
arena representation, the rewriting rule `SetCtorRule` creates the following
SMT constants (assuming that `a, ..., e` were translated to
arena cells):

 - Two cells `c_l` and `c_r` to represent the sets `S` and `T`. These cells are
   backed with two SMT constants of an uninterpreted sort, which corresponds
   to the common type of `S` and `T`.

 - Five SMT constants of the Boolean sort that express set membership of `a, b,
   c` and `d, e` in `S` and `T`, respectively. This cell is backed with an SMT
   constant of the sort of `S` and `T`.

 - One cell `c_u` to represent the set `S \union T`.

 - Five Boolean constants of the Boolean sort that express set membership of
   `a, b, c, d, e` in `S \union T`.

It is obvious that 10 Boolean constants introduced for set membership are
completely unnecessary, as we know for sure that the respective elements belong
to the three sets. Moreover, when constructing `S \union T`, the rule `SetCupRule`
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

With the new representation, the set constructor would simply create five
instances of `FixedElemPtr` that carry the value `true`, that is, the elements
unconditionally belong to `S` and `T`. Further, the rule `SetCupRule` would
simply copy the five pointers, without propagating anything to SMT.

As a result, we obtain constant propagation of set membership, while
keeping the general spirit of the arena-based encoding.

### 3.3. Optimization 2: sharing membership in a powerset

Consider the TLA+ operator that construct the powerset of `S`, that is, the set
of all subsets of `S`:

```tla
SUBSET S
```

Let `c_S` be the cell that represents the set `S` and `c_1, ..., c_n` be the
cells that represent the potential elements of `S`. Note that in general,
membership of all these cells may be unknown in static. For example, consider
the case when the set `S` is constructed from the following TLA+ expression:

```tla
{
  x \in 1..100:
    \E y \in 1..10:
      y * y = x
}
```

In the above example, computation of the predicate is delegated to the SMT
solver.

The code in `PowSetCtor` constructs 2^Cardinality(S) sets that contain all
subsets of `S`. The tricky part here is that some of the elements of `S` may be
outside of `S`. To deal with that, `PowSetCtor` constructs cells for each
potential combinations of `c_1, ..., c_n` and adds membership tests for each of
them. For instance, consider the subset `T` that is constructed by selecting the
indices `1, 3, 5` of `1..n`. The constructor will introduce `3`
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

## 4. Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

[KKT19]: https://dl.acm.org/doi/10.1145/3360549

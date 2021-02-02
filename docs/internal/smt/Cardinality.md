# SMT encoding for set cardinalities

**Author: Igor Konnov, March 2020**

This document contains rationale and the proposal for a better SMT encoding of
the `Cardinality` operator. The encoding of v0.6.0 is explained in the
[OOPSLA19 paper](https://dl.acm.org/doi/10.1145/3360549).  In the following, we
are using the terminology of that paper. Moreover, we use the TLA+ ASCII
notation, wherever possible.

## 1. Problem

Assume that a set `S` is over-approximated with arena cells `c_1, ..., c_n`.
Some of these cells actually belong to the set, and some do not. A Boolean
constant `in_i`, if and only if cell `c_i` belongs to the set `S`.

In the following, we assume that the equality `=` is interpreted on `c_1`, ...,
`c_n` as the structural equality. As Apalache is using lazy equality, we assume
that the equality constraints `c_i = c_j` have been constructed for `i, j \in
1..n`.

## 2. The quadratic encoding in v0.5.0 and v0.6.0

In this encoding, we introduce `n + 1` counters `k_0`, `k_1`, ..., `k_n`. The
counter `k_i` contains the cardinality of the set that is over-approximated
with the cells `c_1`, ..., `c_i`. The counters are defined by the following
equations for `i \in 1..n`.

```tla
k_0 = 0
k_i =  k_{i-1} + (IF in_{i+1} /\ notSeen_i THEN 1 ELSE 0)
```

where the formula `notSeen_i` is defined as follows:

```tla
notSeen_i == \A j \in 1..(i-1): ~in_j \/ c_j /= c_i
```

**Proposition 1.** `Cardinality(S) = k_n`.

**Complexity.** To get an idea of complexity, we count the number of literals
that are produced by this encoding. It is easy to see that every equation for
`k_i` produces `O(i)` literals, `i` inequality tests appear in the formula
`notSeen_i`. If we compute the sum 0 + ... + n - 1, we get `(n - 1) * n`.
Hence, our encoding produces `O(n^2)` literals, that is, it is **quadratic** in
the number of elements that over-approximate `S`.

## 3. A linear encoding for a comparison against a constant in v0.7.0

**Lower bounds.** We have developed a more efficient encoding for the formulas
that have the following form:

```tla
Cardinality(S) >= k,
```

where `S` is a set, and `k` is a constant integer expression.

Essentially, this encoding can be translated into the following formula
`[ExistsForm]`:

```tla
\E x_1, ..., x_k \in S:
  \A y, z \in {x_1, ..., x_k}:
    y /= z
```

We have implemented the translation to the form `[ExistsForm]`. This encoding
introduces intermediate sets such as `{x_1, ..., x_k}`. After that, we have
implemented a direct rewriting rule `CardConstRule`.

**Note.** The translation to `ExistsForm` is only sound, if the expression is
in the positive form, that is, it is not located under any negation. Apalache
automatically computes the negated normal form, so the user does not have to
massage the specification.


**Upper bound.** We have not found a reasonable translation for the formulas of
the form `Cardinality(S) < k`.


## 4. A proposal for a better general encoding (unsound)

**The following encoding is unsound. We are not sure, whether it can be fixed.**

*Enforcing the structural equality `c_i = c_j` requires a set of constraints
that is quadratic in `n`. Given that the equality has been already encoded,
the constraints presented below are linear in `n`.*

**Equivalence classes.**
The new encoding is using uninterpreted functions and constants. We introduce a
fresh sort `Z` whose only elements are uninterpreted constants `z_1`, ...,
`z_n`.  The idea is to map the cells `c_1`, ..., `c_n` on `z_1`, ..., `z_n`, so
that every pair of cells `c_i` and `c_j` is mapped on some `z_k` if and only if
`c_i = c_j`. That is, the constants `z_1`, ..., `z_n` represent the equivalence
classes of the cells `c_1`, ..., `c_n`. (It is possible that some constant `z_i`
represents the empty equivalence class.)

To this end, we introduce two uninterpreted functions:

 - The function `class \in [Sort_C -> Sort_Z]` that maps the cells of the sort
   `C`, which includes the constants `c_1`, ..., `c_n` on the constants of the
   sort `Z`, that is `z_1`, ..., `z_n`.

 - The function `repr \in [Sort_Z -> Sort_C` that maps the constants `z_1`,
   ..., `z_n` on the constants of the sort `C`, which includes the constants
   `c_1`, ..., `c_n`.  This function returns the representative of an
   equivalence class.

**TODO:** *The function `repr` may map a constant `z_k` to a constant that is
not identical to the cells `c_1`, ..., `c_n`. We are using lazy equality in
Apalache. Is it a problem?*

Our goal is to guarantee the following property, which says that the function
`class` is indeed encoding equivalence classes:

```tla
\A i \in 1..n:  c_i = c_j <=> class[c_i] = class[c_j]                   [EquivClass]
```

The direction `c_i = c_j => class[c_i] = class[c_j]` holds true, due to the
**congruence** property of uninterpreted functions.

How do we enforce the other direction? We impose the following constraint:

```tla
\A i \in 1..n: repr[class[c_i]] = c_i                                   [Repr]
```

**Proposition 2.** Condition `[Repr]` implies `class[c_i] = class[c_j] => c_i = c_j`
for `i \in 1..n`.

*Proof:*

Suppose that there is a pair `c_i` and `c_j` that satisfies the conditions:

1. `class[c_i] = class[c_j]`, and

2. `c_i /= c_j`.

    We prove that the existence of such a pair contradicts the condition `[Repr]`.

3. Let `z_i = repr[c_i]` and `z_j = repr[c_j]`.

4. We have `repr[z_i] = repr[z_j]`. Indeed, from Condition 1., we have `z_i = z_j`.
    Hence, by the congruence property applied to `repr`

    Let `c_k = repr[z_i]` and `c_l = repr[z_j]`. We have the following:

5. `c_k = c_l` by Condition 4.

6. `c_k = repr[class[c_i]] = c_i`. By Condition 2.

7. `c_l = repr[class[c_j]] = c_j`. By Condition 2.

8. Finally, `c_i = c_j`. By 5.-7. This contradicts with the assumption `c_i /= c_j`.

*QED*

By combining Proposition 2 with congruence of `class`, we obtain the desired
property `[EquivClass]`. Hence, the functions `class` and `repr` provide us
with a way to compute equivalence classes.

**Set membership.** It remains to take the membership relation into account.
That is, we would like to use as representatives only the cells that actually
belong to the set `S`. To this end, we introduce an uninterpreted `cin \in [Sort_C
-> BOOLEAN]`, which for every `c_i` encodes, whether `c_i`
belongs to the set `S`. This uninterpreted function is identical to the Boolean
variables `in_1`, ..., `in_n`, that is, the following constraint holds true,
for i \in 1..n:

```tla
cin[c_i] = in_i        [DefCin]
```

The purpose of the function `cin` is solely to use congruence of the set
membership relation.

**BUG:** It might happen that a pair of equal cells `c_i` disagree
on the set membership, that is, `c_i = c_j/\ in_i /\ ~in_j` holds true.

**Cardinality computation.**  Finally, we count the number of equivalence
classes that satisfy the following predicate `isCounted_i` for `i \in 1..n`:

```tla
class[repr[z_i]] = z_i /\ cin[repr[z_i]]
```

**NOTE:** It might happen that `repr[z_i]` is mapped on a constant `d` that is
syntactically different from `c_1`, ..., `c_n`. This, however, does not pose
a problem, as the congruence property of `cin` enforces `cin[c_i] = cin[d]`.

We introduce equations to count the number of equivalence classes for `i \in 1..n`:

```tla
    /\ k_0 = 0
    /\ isCounted => k_i = k_{i-1} + 1
    /\ ~isCounted => k_i = k_{i-1}
```

By collecting the constraints in this section, `[DefCin]` and `[Repr]`, we have
a complete set of constraints for computing `k_n = Cardinality(S)`. As one can
see, the number of literals in this encoding is **linear**, that is, `O(n)`.

**NOTE:** Although the number of constraints is linear, we have to analyze complexity
of the underlying SMT problem, which may happen to be as hard as the SMT problem
that is constructed in v0.6.0.


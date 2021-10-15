# ADR-011: alternative SMT encoding using arrays

| author        | revision |
| ------------- | --------:|
| Rodrigo Otoni |        1 |

This ADR describes an alternative encoding of the [KerA+] fragment of TLA+ into SMT.
Compound data structures, e.g. sets, are currently encoded using [uninterpreted functions],
with the goal being to encode them using [arrays with extensionality] instead.
The hypothesis is that this will lead to increased solver performance and more compact SMT instances.
We target the [Z3] solver and will use the [SMT-LIB Standard] ([Version 2.6]) in conjunction
with Z3-specific operators, e.g. constant arrays.

For an overview of the current encoding check the [TLA+ Model Checking Made Symbolic] paper,
presented at OOPSLA'19. In the remainder of the document the use of the new encoding and the
treatment of different TLA+ operators are described.

## 1. CLI encoding option

The encoding using arrays is to be an alternative, not a replacement, to the already existing encoding.
Given this, a new option is to be added to the `check` command of the CLI. The default encoding will be
the existing one. The option description is shown below.

```
--smt-encoding=STRING   : the SMT encoding: oopsla19, arrays (experimental), default: oopsla19
```

### Code changes

The following changes will be made to implement the new CLI option:

- Add new string variable to class `CheckCmd` to enable the new option.
- Add new class `Z3SolverContextForArrays`, which extends class `Z3SolverContext`.
- Add new class `SymbStateRewriterImplWithArrays`, which extends class `SymbStateRewriterImpl`.
- Use the new option to select between different `SolverContext` and `SymbStateRewriter`
  implementations in classes `BoundedCheckerPassImpl`,  `RecordingSolverContext`,
  `PreproSolverContext`, and `SymbStateRewriterAuto`.

## 2. Testing the new encoding

The new encoding should provide the same results as the existing one, the available test suit
will thus be used to test the new encoding. To achieve this, the test suit will be made parametric
w.r.t. the implementations of the `SolverContext` and `SymbStateRewriter`.

### Code changes

The following changes will be made to implement the parametric testing:

- Refactor the classes in `tla-bmcmt/src/test` to enable testing with different
  implementations of `SolverContext` and `SymbStateRewriter`.

## 3. Encoding sets

Sets are currently encoded in an indirect way. Consider a sort `some_sort` and distinct elements `elem1`,
`elem2`, and `elem3` of type `someSort`, as defined below.

```
(declare-sort some_sort 0)
(declare-const elem1 some_sort)
(declare-const elem2 some_sort)
(declare-const elem3 some_sort)

(assert (distinct elem1 elem2 elem3))
```

A set `set1` containing `elem1`, `elem2`, and `elem3` is currently represented by a constant of type 
`set_of_some_Sort` and three membership predicates, as shown below.

```
(declare-sort set_of_some_Sort 0)
(declare-const set1 set_of_some_Sort)

(declare-const elem1_in_set1 Bool)
(declare-const elem2_in_set1 Bool)
(declare-const elem3_in_set1 Bool)

(assert elem1_in_set1)
(assert elem3_in_set1)
(assert elem2_in_set1)
```

The new encoding has each set encoded directly as an array whose domain and range equal the set's sort
and the Boolean sort, respectively. SMT arrays can be thought of as a functions, as this is exactly how
they are [represented internally in Z3]. Set membership of an element `elem` is thus attained by simply
setting the array at index `elem` to `true`.

One important point in the new encoding is the handling of set declarations, since declaring an
empty set requires the setting of all array indexes to false. This can be easily achieved for
finite sets by explicitly setting each index, but falls outside the quantifier-free fragment of
first-order logic in the case of infinite sets, e.g. the set of integers. To handle declarations
of infinite sets we rely on Z3's constant arrays, which map all indexes to a fixed value. Below is
an example using the new encoding.

```
(declare-const set2_0 (Array some_sort Bool))
(declare-const set2_1 (Array some_sort Bool))
(declare-const set2_2 (Array some_sort Bool))
(declare-const set2_3 (Array some_sort Bool))

(assert (= set2_0 ((as const (Array some_sort Bool)) false)))

(assert (= set2_1 (store set2_0 elem1 true)))
(assert (= set2_2 (store set2_1 elem2 true)))
(assert (= set2_3 (store set2_2 elem3 true)))
```

The `store` operator handles array updates and receives the array to be updated, the index, and the new
value, returning the updated array. For array access, the `select` operator can be used, which receives
an array and an index and returns the value at the given index, as shown below.

```
(assert (= (select set2_2 elem1) true)) ; SAT
(assert (= (select set2_2 elem2) true)) ; SAT
(assert (= (select set2_2 elem3) true)) ; UNSAT

(assert (= (select set2_3 elem1) true)) ; SAT
(assert (= (select set2_3 elem2) true)) ; SAT
(assert (= (select set2_3 elem3) true)) ; SAT
```

For consistency, the new encoding uses constant arrays to declare both finite and infinite arrays.

### Code changes

The following changes will be made to implement the new encoding of sets:

- Add alternative rewriting rules for sets, via new classes extending `RewritingRule`.
- In class `SymbStateRewriterImplForArrays`, overwrite rules pertaining to sets in `ruleLookupTable`.
- In class `Z3SolverContextForArrays`, overwrite appropriate methods.

## 4. Encoding tuples and records

TODO

## 5. Encoding functions and sequences

TODO

## 6. Encoding control operators and TLA+ quantifiers

TODO

[KerA+]: https://apalache.informal.systems/docs/apalache/kera.html
[uninterpreted functions]: http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_UF
[arrays with extensionality]: http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml
[Z3]: https://github.com/Z3Prover/z3
[SMT-LIB Standard]: http://smtlib.cs.uiowa.edu/index.shtml
[Version 2.6]: https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
[TLA+ Model Checking Made Symbolic]: https://dl.acm.org/doi/10.1145/3360549
[represented internally in Z3]: https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-arrays

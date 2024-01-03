# ADR-011: alternative SMT encoding using arrays

| author        | revision |
| ------------- |---------:|
| Rodrigo Otoni |      1.8 |

This ADR describes an alternative encoding of the [KerA+] fragment of TLA+ into SMT.
Compound data structures, e.g. sets, are currently encoded using the [core theory] of SMT,
with the goal being to encode them using [arrays with extensionality] instead.
The hypothesis is that this will lead to increased solver performance and more compact SMT instances.
We target the [Z3] solver and will use the [SMT-LIB Standard] ([Version 2.6]) in conjunction
with Z3-specific operators, e.g. constant arrays.

For an overview of the current encoding check the [TLA+ Model Checking Made Symbolic] paper,
presented at OOPSLA'19. In the remainder of the document the use of the new encoding and the
treatment of different TLA+ operators are described. For further details on the new encoding
check the [Symbolic Model Checking for TLA+ Made Faster] paper, presented at TACAS'23.

## 1. CLI encoding option

The encoding using arrays is to be an alternative, not a replacement, to the already existing encoding.
Given this, a new option is to be added to the `check` command of the CLI. The default encoding will be
the existing one. The option description is shown below. The envvar `SMT_ENCODING` can also be used to
set the encoding, see the [model checking parameters] for details. In addition to the `arrays` encoding,
which uses SMT arrays to encode TLA+ sets and functions, we also have the `funArrays` encoding, which
restricts itself to encoding only TLA+ functions as SMT arrays.

```
--smt-encoding : the SMT encoding: oopsla19, arrays (experimental), funArrays (experimental), default: oopsla19 (overrides envvar SMT_ENCODING)
```

### Code changes

The following changes will be made to implement the new CLI option:

- Add new string variable to class `CheckCmd` to enable the new option.
- Add new `smtEncoding` field to `SolverConfig`.
- Add new class `SymbStateRewriterImplWithArrays`, which extends class `SymbStateRewriterImpl`.
- Use the new option to set the `SolverConfig` encoding field and select between different `SymbStateRewriter`
  implementations in classes `BoundedCheckerPassImpl` and `SymbStateRewriterAuto`.
- The infrastructure changes made for the `funArrays` encoding mirror the ones made for the `arrays` one.
  See [PR 2027] for details.

## 2. Testing the new encoding

The new encoding should provide the same results as the existing one, the available test suite
will thus be used to test the new encoding. To achieve this, the unit tests needs to be made parametric
w.r.t. the `SolverConfig` encoding field and the implementations of `SymbStateRewriter`, and the
integration tests need to be tagged to run with the new encoding.

### Code changes

The following changes will be made to implement the tests for the new encoding:

- Refactor the classes in `tla-bmcmt/src/test` to enable unit testing with different configurations
  of `SolverConfig` and implementations of `SymbStateRewriter`.
- Add unit tests for the new encoding, which should be similar to existing tests, but use a
  different solver configuration and `SymbStateRewriterImplWithArrays` instead of `SymbStateRewriterImpl`.
- Add integration tests for the new encoding by tagging existing tests with `array-encoding`, which
  will be run by the CI with envvar `SMT_ENCODING` set to `arrays`.

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

- Add alternative rewriting rules for sets when appropriate, by extending the existing rules.
  - All alternative rules will be suffixed with `WithArrays`.
  - The new rules will not rely on `LazyEquality` and will aim to use SMT equality directly.
  - Only the generation of SMT constraints will be modified by the new rules, the other Arena
    elements will remain unchanged.
- In class `SymbStateRewriterImplWithArrays`, add the new rules to `ruleLookupTable` by overriding
  the entries to their older versions.
- Add four new Apalache IR operators in `ApalacheOper`, `Builder`, `ConstSimplifierForSmt`, and 
  `PreproSolverContext`, to represent the array operations.
  - The `selectInSet` IR operator represents the SMT `select`.
  - The `storeInSet` IR operator represents the SMT `store`.
  - The `unchangedSet` IR operator represents an equality between the current and new SSA array
    representations. This is required to constraint the array representation as it evolves. It is
    important to note that this operator assumes that all arrays are initially empty, so an element
    not explicitly added is assumed to not be in the array. To check absence of an element,
    `selectInSet` should be used with negation.
  - The `smtMap` IR operator represents the use of SMT map.
- In class `Z3SolverContext`, add/change appropriate methods to handle SMT constraints over arrays.
  - The main changes will de done in `declareCell` and the new `mkSelect`, `mkStore`, and 
    `mkUnchangedSet` methods, as these methods are directly responsible for creating the SMT 
    constraints representing sets and set membership.
  - With the new IR operators, the "in-relation" concept, which underpins `declareInPredIfNeeded` 
    and `getInPred`, will not be applied to the new encoding. Cases for the new IR operators will 
    be added to `toExpr`, which will default to `TlaSetOper.in` and `TlaSetOper.notin` for the 
    existing encoding.
  - The `smtMap` IR operator will be used to encode the TLA+ set filter operation. It constructs
    a temporary array that contains the evaluation of the filter's predicate for each set element
    and uses SMT map to compute the intersection of the set being filtered and the set represented
    by the temporary array constructed.
  - Cases for `FinSetT` and `PowSetT` will be added to `getOrMkCellSort`, as these types are no
    longer represented by uninterpreted constants.
  - `cellCache` will be changed to contain a list of cells, in order to handle the effects of
    `push` and `pop` in the SSA assignment of sets. The following examples illustrates this need.
    ```
    (assert (= set_0 ((as const (Array Int Bool)) false)))
    (assert (= set_1 (store set_0 5 true)))
    (push)
    (assert (= set_2 (store set_1 6 true)))
    (push)
    (assert (= set_3 (store set_2 7 true)))
    (assert (= (select set_3 7) true))
    (pop 2)
    (assert (= (select set_1 7) false)) ; Without the list we would query set_3 here 
    ```

## 4. Encoding functions and sequences

Functions are currently encoded as sets of pairs, with each pair representing a mapping present in
the function. The first element of a pair is a tuple containing some function arguments and the second
element is the return value given by such arguments. The handling of functions is thus given by 
operations over sets and tuples. Sequences of type `T` are currently encoded as tuples of form
`⟨start,end,fun⟩`, where `start` and `end` are integers and `fun` is a function from integers to `T`.
The new encoding of functions will thus encompass sequences, as their tuple representations is
intended to be kept.

The new encoding will, like the current one, also map tuples of arguments to return values, but
will do so natively instead of simply relying on sets. A function will be represented by two SMT
arrays. The first array will store the domain of the function and will be encoded as a standard 
TLA+ set. The second array will store the mappings, having sort `<S1,...,Sn>` as its domain, with
`Si` being the sort of argument `i`, and the sort of the function's codomain as its range. 
The sorts of the array domain and range can be infinite, but the domain of the function itself,
and by implication the number of mappings tuples, will always be finite.

To encode the TLA+ function `finSucc = [x \in {1,2,3} |-> x + 1 ]`, which computes the successors
of integers from `1` to `3`, we first have to declare its domain, as shown below; tuples are
represented here as per the OOPSLA'19 encoding.

```
(declare-sort Tuple_Int 0) ; Sort of <Int>
(declare-const tuple_with_1 Tuple_Int) ; <1>
(declare-const tuple_with_2 Tuple_Int) ; <2>
(declare-const tuple_with_3 Tuple_Int) ; <3>

(declare-const finSucc_domain_0 (Array Tuple_Int Bool))
(declare-const finSucc_domain_1 (Array Tuple_Int Bool))
(declare-const finSucc_domain_2 (Array Tuple_Int Bool))
(declare-const finSucc_domain_3 (Array Tuple_Int Bool))

(assert (= finSucc_domain_0 ((as const (Array Tuple_Int Bool)) false)))  ; {}
(assert (= finSucc_domain_1 (store finSucc_domain_0 tuple_with_1 true))) ; {<1>}
(assert (= finSucc_domain_2 (store finSucc_domain_1 tuple_with_2 true))) ; {<1>,<2>}
(assert (= finSucc_domain_3 (store finSucc_domain_2 tuple_with_3 true))) ; {<1>,<2>,<3>}
```

The array storing the function's domain is used to guard the definition of the array storing the
function's mappings, since mappings should only be present for values in the domain. The array
storing the mappings of `finSucc` is shown below.

```
(declare-const finSucc_0 (Array Tuple_Int Int))
(declare-const finSucc_1 (Array Tuple_Int Int))
(declare-const finSucc_2 (Array Tuple_Int Int))
(declare-const finSucc_3 (Array Tuple_Int Int))

(assert (ite (select finSucc_domain_3 tuple_with_1)
             (= finSucc_1 (store finSucc_0 tuple_with_1 2))
             (= finSucc_1 finSucc_0)))
(assert (ite (select finSucc_domain_3 tuple_with_2)
             (= finSucc_2 (store finSucc_1 tuple_with_2 3))
             (= finSucc_2 finSucc_1)))
(assert (ite (select finSucc_domain_3 tuple_with_3)
             (= finSucc_3 (store finSucc_2 tuple_with_3 4))
             (= finSucc_3 finSucc_2)))
```

Note that, unlike with the new encoding for sets, we do not use constant arrays. The reason is that
the function's domain cannot be altered, so the array has to constrain only the values in said domain.
Function application can be done by simply accessing the array at the index of the passed arguments.
A function application with arguments outside the function's domain leads to an unspecified result in
TLA+, which is perfectly captured by unconstrained entries in the SMT array. Below are some examples
of function application.

```
(assert (= (select finSucc_3 tuple_with_1) 2)) ; SAT
(assert (= (select finSucc_3 tuple_with_2) 3)) ; SAT
(assert (= (select finSucc_3 tuple_with_3) 4)) ; SAT

(declare-const tuple_with_4 Tuple_Int) ; <4>
(assert (= (select finSucc_3 tuple_with_4) 16)) ; SAT
```

Although a function's domain cannot be altered, its image can be changed via the TLA+ function
update operator. The update will be encoded as a guarded array update, as illustrated below;
attempting to update an entry outside the function's domain will lead to no change happening.

```
(declare-const finSucc_4 (Array Tuple_Int Int))
(declare-const finSucc_5 (Array Tuple_Int Int))

(assert (ite (select finSucc_domain_3 tuple_with_1) ; [finSucc EXCEPT ![1] = 9]
             (= finSucc_4 (store finSucc_3 tuple_with_1 9))
             (= finSucc_4 finSucc_3)))
(assert (ite (select finSucc_domain_3 tuple_with_4) ; [finSucc EXCEPT ![4] = 25]
             (= finSucc_5 (store finSucc_4 tuple_with_4 25))
             (= finSucc_5 finSucc_4)))

(assert (= (select finSucc_5 tuple_with_1) 2))  ; UNSAT
(assert (= (select finSucc_5 tuple_with_1) 9))  ; SAT
(assert (= (select finSucc_5 tuple_with_4) 16)) ; SAT
```

In contrast to the current encoding, which produces a number of constraints that is linear in the
size of the set approximating the function when encoding both function application and update,
the new encoding will produce a single constraint for each operation. This will potentially lead
to a significant increase in solving performance.

### Code changes

The following changes will be made to implement the new encoding of functions:

- Add alternative rewriting rules for functions when appropriate, by extending the existing rules. The
  same caveats stated for the rewriting rules for sets will apply here.
  - The sets of pairs used in the current encoding are the basis for the counter-example generation in
    `SymbStateDecoder`. In order to continue having counter-examples, these sets will keep being produced,
    but will not be present in the SMT constraints. They will be carried only as metadata in the `Arena`.
- Update class `SymbStateRewriterImplWithArrays` with the rules for functions.
- Update the `storeInSet` IR operator to also store function updates. It will have the value resulting
  from the update as an optional argument.
  - Since functions will be encoded as SMT arrays, the `selectInSet`, `storeInSet`, and `unchangedSet`
    IR operators will be used when handling them. A future refactoring may rename these operators.
- Update class `Z3SolverContext` to handle the new SMT constraints over arrays.
  - A case for `FunT` will be added to `getOrMkCellSort`.
  - In `declareCell`, functions will be declared as arrays, but will be left unconstrained.
  - The `mkStore` method will be updated to also handle functions. It will have an additional
    optional argument containing the value to be stored in the range of the array. The new
    argument's default value is `true`, for the handling of sets.
  - The `mkNestedSelect` method is added to support set membership in function sets, i.e.,
    `f \in [S -> T]`. The nesting has first `funAppRes = f[s \in S]`, followed by `funAppRes \in T`.

## 5. Encoding the remaining TLA+ features

The use of SMT arrays will be restricted to TLA+ sets and functions for the moment. The encoding of
additional features using SMT arrays, or potentially ADTs, will be left for the future.

[KerA+]: https://apalache.informal.systems/docs/apalache/kera.html
[core theory]: http://smtlib.cs.uiowa.edu/theories-Core.shtml
[arrays with extensionality]: http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml
[Z3]: https://github.com/Z3Prover/z3
[SMT-LIB Standard]: http://smtlib.cs.uiowa.edu/index.shtml
[Version 2.6]: https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
[TLA+ Model Checking Made Symbolic]: https://dl.acm.org/doi/10.1145/3360549
[Symbolic Model Checking for TLA+ Made Faster]: https://doi.org/10.1007/978-3-031-30823-9_7
[model checking parameters]: https://apalache.informal.systems/docs/apalache/running.html#model-checker-command-line-parameters
[represented internally in Z3]: https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-arrays
[PR 2027]: https://github.com/informalsystems/apalache/pull/2027

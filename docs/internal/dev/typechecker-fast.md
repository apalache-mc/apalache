# Fast ETC Type Checker

This note explains the fast implementation of ETC in
`tla-typechecker/src/main/scala/at/forsyte/apalache/tla/typecheck/etcfast/EtcTypeCheckerFast.scala`.
It is intended for developers and researchers who need to reason about the
algorithm, its invariants, and its differences from the legacy
`etc.EtcTypeChecker`.

The public contract is unchanged: the checker consumes an `EtcExpr`, a
`TypeContext`, and a `TypeCheckerListener`, and returns `Some(TlaType1)` for a
well-typed expression or `None` after reporting type errors.

## Background

The legacy ETC checker translates a TLA+ module into an `EtcExpr`, collects
constraints, and solves them by repeatedly replaying substitutions. This is
simple and robust, but large modules produce many constraints and large
substitutions. Repeatedly applying a substitution to a growing constraint set is
the main source of poor asymptotic behavior.

The fast checker keeps the same front-end translation and the same external type
model, but changes the internal solver architecture:

1. Translate TLA+ to `EtcExpr` as before.
2. Traverse the `EtcExpr` once.
3. Allocate internal mutable type variables on demand.
4. Mutate one live inference graph as equalities are discovered.
5. Export the final internal graph back to `TlaType1`.

Conceptually, this is Hindley-Milner style inference over the ETC language,
extended with Apalache-specific delayed overload resolution.

## Internal Type Graph

The checker converts every external `TlaType1` into an internal `FType` graph.
The important internal nodes are:

```scala
TVar(id, level, link, canonicalPositiveId)
FSet(elem)
FSeq(elem)
FFun(arg, res)
FOper(args, res)
FTup(elems)
FSparseTup(fields)
FRec(fields)
FRow(fields, tail)
FRecRow(row)
FVariant(row)
```

`TVar` is the mutable part of the representation. A variable may be unbound, in
which case `link = None`, or bound to another type, in which case `link =
Some(target)`. Calling `prune` follows links and applies path compression.

The intended equivalence relation is:

$$
t_1 \sim t_2 \quad \text{iff unification has made } t_1 \text{ and } t_2
\text{ equal in the live graph.}
$$

For unbound variables, the representative is the pruned `TVar`. For a variable
bound to a structure, the representative is that pruned structure.

### Levels

Every fresh variable receives an HM level. Variables allocated inside a LET
definition have a greater level than variables in the surrounding environment.
When a younger variable is linked into an older type, `lowerLevels` lowers all
reachable unbound variables to the older level.

The current implementation generalizes by comparing the free variables of the
definition against the free variables of the surrounding environment, rather
than by using the level directly:

$$
\mathrm{generalize}(E, t) =
\forall(\mathrm{fv}(t) \setminus \mathrm{fv}(E)).\ t
$$

The level still matters operationally because it prevents accidental escape of
younger variables through links.

### Canonical External Variable Names

Internal variables may be fresh or derived from existing `VarT1` names. The
checker preserves legacy compatibility by exporting the smallest positive
variable number in an equivalence class whenever possible. This is tracked by
`canonicalPositiveId`.

When no positive external id is available, `exportType` assigns a fresh positive
number during export. This keeps negative or internal-only ids out of
user-visible `TlaType1` values.

## Main Inference Function

The core function is:

```scala
infer(env: FastEnv, level: Int, ex: EtcExpr, expected: Option[FType]): FType
```

The `expected` argument carries contextual information downward. It is not a
complete bidirectional type checker, but it is essential for resolving overloads
whose result type is fixed by an enclosing expression.

Important cases:

* `EtcConst(polytype)` converts the external type into the internal graph.
* `EtcTypeDecl(name, declaredType, body)` extends the environment with a scheme.
* `EtcName(name)` instantiates the scheme in the environment.
* `EtcAbs(body, binders*)` infers binder element types, checks that binder
  domains are sets, and returns an `FOper`.
* `EtcApp(signatures, args*)` infers an application, possibly delaying overload
  resolution.
* `EtcAppByName(name, args*)` instantiates the named operator and delegates to
  application inference.
* `EtcLet(name, lambda, body)` infers and generalizes a user operator
  definition, then checks the body under the generalized scheme.

The checker reports discovered types lazily through `watchType`. These callbacks
are delayed until inference has stabilized, because a type found early may still
be refined by later unifications.

## Unification

Unification mutates the live graph. It is implemented by:

```scala
unify(left: FType, right: FType): Unit
bindVar(variable: TVar, other: FType): Unit
```

The algorithm first prunes both sides. If one side is an unbound variable, the
variable is linked to the other side after an occurs check. If both sides are
structures, unification proceeds recursively.

The critical invariant is:

$$
\mathrm{after}\ \mathrm{unify}(a,b),\quad
\mathrm{exportType}(a) = \mathrm{exportType}(b)
$$

modulo canonical renaming of type variables.

### Records and Sparse Tuples

Legacy ETC treats closed record and sparse tuple unification as a structural
join. For records:

$$
[f_i : A_i]_{i \in I} \sqcup [f_j : B_j]_{j \in J}
$$

has fields $I \cup J$. Shared fields must unify; non-shared fields are kept.
For example:

```tla
[x: Int]  ~  [y: Bool]  ==>  [x: Int, y: Bool]
```

Sparse tuples behave similarly, except that a sparse tuple unified with a
concrete tuple may not mention indices outside the concrete tuple domain. Thus
`<| 3: Int |>` does not unify with `<<Int, Int>>`.

Rows are handled separately by `unifyRows`, which follows the row-polymorphic
typing rules used by records and variants in Type System 1.2.

## LET Polymorphism

LET definitions are inferred as operator definitions. For:

```tla
LET F(x) == body IN scope
```

the checker:

1. Finds an annotation scheme for `F`, or creates a fresh operator scheme.
2. Extends the environment with `F` before checking the body. This supports
   recursive references in the same style as legacy ETC.
3. Translates binders into parameter types by checking membership domains.
4. Infers `body`.
5. Unifies the inferred operator type with the annotation scheme.
6. Resolves overloads created inside this definition.
7. Generalizes the resulting definition type against the outer environment.
8. Checks `scope` with `F` bound to the generalized scheme.

Generalization is the usual HM operation:

$$
\sigma_F = \forall \alpha_1,\ldots,\alpha_n.\ \tau_F
$$

where the quantified variables are free in the inferred definition type but not
free in the surrounding environment.

If `inferPolytypes = false`, any non-empty quantified set is reported as an
error.

## Overload Resolution

Many TLA+ constructs are translated into overloaded ETC applications. Examples
include:

* tuple vs. sequence literals,
* function vs. sequence vs. record vs. tuple application,
* `DOMAIN`,
* row-typed record operations.

For an application with signatures

$$
s_1,\ldots,s_n
$$

and inferred application type

$$
(\tau_1,\ldots,\tau_k) \Rightarrow \rho,
$$

the checker computes compatible signatures by asking whether each external
signature unifies with the exported current application type. This compatibility
probe is side-effect-free with respect to the live inference graph.

There are three cases:

* exactly one compatible signature: commit it into the live graph;
* no compatible signatures: report a type error;
* multiple compatible signatures: postpone the application.

Postponed applications are stored in `pendingApps`. They are revisited to a
fixpoint after new constraints may have refined argument or result types.

### Why Probes Must Be Side-Effect-Free

A failed or ambiguous overload probe must not mutate live variables. Otherwise,
testing a candidate such as `Int => Int` can accidentally force an unresolved
argument to `Int`, making a later candidate or enclosing expression appear
deterministic when it is not.

The checker therefore uses `TypeUnifier` over exported `TlaType1` values for
compatibility checks. Only after a unique signature is selected does
`commitResolvedOverload` instantiate the selected signature into live variables
and unify it with the live application type.

### LET-Local Pending Scope

When checking a LET definition, the checker must resolve overloads introduced by
that definition before it generalizes the definition type. However, it must not
force unrelated pending overloads that belong to an enclosing expression. Those
may still be waiting for the enclosing expression to push down an expected type.

The implementation records the pending-app index at the start of a LET and only
fails ambiguities created after that index. At the end of the whole `compute`
call, all remaining ambiguities are failed.

## Listener Compatibility

The public checker API communicates type information through
`TypeCheckerListener`. The fast checker delays callbacks with:

```scala
watchedTypes: LinkedHashMap[UID, (ExactRef, () => TlaType1)]
```

This has two purposes:

1. callback types are exported after inference has stabilized;
2. insertion order remains deterministic enough for tests and downstream code.

`protectedTypes` prevents wrapper expressions from overwriting the type of
declarations or operators that share the same UID in the ETC encoding. This is
compatibility bookkeeping rather than part of the inference algorithm.

On an operator-definition failure, the checker preserves the legacy follow-up
diagnostic:

```text
Error when computing the type of X
```

except for generated module wrappers.

## Export Boundary

The fast checker is intentionally internal. The rest of Apalache should not see
`FType`, `TVar`, links, or levels. The boundary is:

```scala
FType  --exportType-->  TlaType1
TlaType1Scheme  --fromExternalScheme-->  FastScheme
```

This boundary is also where the checker preserves legacy conventions:

* external type variables use positive `VarT1` numbers;
* the smallest positive id in an equivalence class is preferred;
* row tails are exported as `RowT1(..., Some(VarT1(n)))`;
* all listener callbacks report `TlaType1`.

## Complexity Intuition

The legacy solver repeatedly applied substitutions over collected constraints.
In the worst cases, this makes each new equality pay for a large prefix of the
previous work.

The fast checker instead stores equalities in the graph:

* variable links are followed with path compression;
* structure unification only descends into the relevant substructure;
* delayed overload checks are revisited only when ambiguity remains.

This does not make all cases linear. Overloaded operators still create a product
of signatures and applications, and exporting large types for compatibility
probes has a cost. The important win is that ordinary equality propagation does
not require rebuilding and replaying a large global substitution.

## Testing Expectations

The fast checker should be tested against the legacy ETC semantics unless a
difference is explicitly documented. Important regression categories are:

* unresolved type variables should not become fixed by overload probes;
* enclosing expected types should resolve tuple-vs-sequence ambiguity;
* LET-local overload resolution should not fail enclosing pending overloads;
* records with non-overlapping fields should join;
* sparse tuples should reject out-of-domain indices when unified with concrete
  tuples;
* row-typed records and variants should behave like `TypeUnifier`.

The shared tests in `TestEtcTypeCheckerBase` are the first line of defense,
because they run against both the legacy and fast implementations.

## Useful Entry Points

* `TypeCheckerTool.check`: selects `EtcTypeCheckerFast` by default.
* `ToEtcExpr`: translates TLA+ declarations and expressions into `EtcExpr`.
* `EtcTypeCheckerFast.infer`: main recursive inference function.
* `EtcTypeCheckerFast.unify`: live graph unifier.
* `EtcTypeCheckerFast.compatibleOverloads`: side-effect-free overload probe.
* `EtcTypeCheckerFast.resolvePendingApps`: delayed overload fixpoint.
* `EtcTypeCheckerFast.exportType`: internal-to-external type boundary.

# Java APIs for Apalache IR

The Java 21 APIs expose Apalache's existing IR carriers without requiring Scala
interop in consumer code. All library versions must match:

- `org.apalache-mc:tla-ir-java` — builders, types, inspection, transformations and
  unification (`org.apalache_mc.tla.jir`); depends only on the core IR project.
- `org.apalache-mc:tla-io-java` — text and typed JSON (`org.apalache_mc.tla.jio`);
  adds the I/O library, not the parser, full typechecker or native solvers.

Scala remains a transitive runtime dependency. This is not an opaque Java AST:
`TlaEx`, `TlaType1`, their concrete subtypes and declarations remain the core IR
objects. Pattern matching and scalar accessors such as `body()` and `name()` are
supported; prefer facade accessors over Scala collections such as `args()`.

## Construct, inspect and serialize

```java
var b = new TlaTypedScopeUncheckedBuilder();
var expression = b.plus(b.integer(40), b.integer(2));
var declaration = b.decl("Answer", expression);
var module = TlaModules.create("Example", List.of(declaration));

TlaType1 type = TlaTypes.typeOf(expression);
List<TlaEx> arguments = TlaExpressions.arguments((OperEx) expression);
assert ((OperEx) expression).oper() == TlaOperators.PLUS;
var text = new TlaText(80, 2);
String source = text.render(writer -> text.writeWithStandard(module, writer));
TlaModule decoded = TlaJson.readModule(TlaJson.writeModule(module, 2));
```

Use `TlaTypes.INT`, `BOOL`, `STRING`, `REAL`, and the structural factories rather
than Scala singleton access. Open row/record/variant factories accept a `VarT1`
as well as the existing string form. `rowFields` is sorted by field name;
`rowTail` returns a Java `Optional`. Type children are ordered structurally:
positional arguments before result, sorted row fields before tail, record and
variant wrappers before their row. `typeOf` rejects untyped/non-TLA-type tags
with `TlaBuilderTypeException` rather than guessing a type.

Collection accessors return immutable snapshots, not deep copies of elements.
Module assembly preserves declaration order and retains the supplied IR objects.
`TlaDeclarations.parameters` derives typed parameters from the operator tag and
validates counts and higher-order parameter arities.

`TlaOperators` exposes underlying singleton identities. It excludes internal
operators, deprecated `withType`, and the `FunAsSeq`/`SelectSeq` placeholders whose
upstream initializers deliberately throw; the latter are represented by rewired
TLA definitions rather than these IR singletons.

## Transformations and ownership

`TlaExpressions.forEach` visits occurrences in preorder, with LET body before
local declaration bodies. Shared occurrences are visited repeatedly.

`rewrite` is bottom-up, preserves tags and recursion flags, and rebuilds compound
nodes and local declarations while sharing unchanged leaves. Callback replacements
are not recursively traversed; null replacements fail. `deepCopy` instead gives
fresh IDs to all copyable expression/declaration nodes, including name/value
leaves, and shares no mutable declarations. The core singleton `NullEx` remains
shared. A callback returning a shared mutable object owns that decision.

`withName`, `withArguments`, `withLocalDeclarations`, `withHeader`, and `withBody`
are structural reconstruction operations, not typed builders. They preserve
original tags without type inference or scope validation, including polymorphic
imported tags. Header renaming does not rewrite the body. Callers are responsible
for consistent renaming, scope, valid types and ownership of retained references.

## Type operations

```java
var a = TlaTypes.typeVariable(0);
var substitution = TlaTypeSubstitution.of(Map.of(0, TlaTypes.INT));
TlaType1 concrete = substitution.applyFully(TlaTypes.set(a));
var match = new TlaTypeUnifier().unify(Optional.empty(), a, TlaTypes.INT).orElseThrow();
```

`applyOnce` performs simultaneous substitution; `applyFully` substitutes to
convergence and requires acyclic assignments. Do not use recursive substitution
for alpha-renaming. Invalid row assignments and nonconvergence propagate failures.

Pass `Optional.empty()` when there is no initial substitution. When unifying only
an operator's result, construct the unifier with its complete signature so fresh
variables cannot collide with argument-only variables:

```java
var unifier = new TlaTypeUnifier(signature);
var match = unifier.unify(Optional.empty(), signature.res(), requestedType);
```

Fresh IDs are above the maximum reserved ID, including IDs in the initial
substitution. Exhausted IDs fail explicitly. Each call is independent, and
substitutions are reusable. Ordinary mismatch returns `Optional.empty()`.
Unification can widen record rows; callers requiring an exact result must compare
`unifiedType` with their requested type.

## I/O contracts

Construct `TlaText` with a text width and indentation size. Its `write` methods
write expressions without declaration annotations and modules with declaration
type annotations. Module rendering uses the upstream standard EXTENDS list unless
explicit modules are supplied. The methods accept caller-owned `PrintWriter`
instances and never close or flush them. The single `render` method captures any
write operation as a string:

```java
String source = text.render(writer -> text.writeWithStandard(module, writer));
```

Printers and annotation stores are per-call and owned internally.

`TlaJson` uses the direct typed-tag reader, not the builder-backed reader: imported
polymorphic empty-set tags must not be reconstructed as sets of sets. JSON syntax
and IR decoding failures are wrapped in `TlaJsonException` with their cause. The
reader requires exactly one module. Writer indentation is explicit: `-1` selects
compact output and nonnegative values select pretty printing. The writer does not
strip labels or normalize expressions. File handling and size limits remain caller policy.

This branch's shared operator registry now recognizes LABEL for direct JSON
round trips. This does not change readers in previously released distributions;
consumers targeting an older checker may still need their existing compatibility
normalization until that distribution is upgraded.

## Full-distribution tool invocation

The full distribution's existing `at.forsyte.apalache.tla.Tool` class has a
stream-aware overload:

```java
int status = Tool.run(arguments, diagnostics, diagnostics);
```

It returns exit codes, including invalid CLI arguments, without invoking
`System.exit`. It redirects Java and Scala console streams and restores them on
success or failure without closing caller streams. Other tool failures propagate.
Calls must be sequential in an isolated worker JVM: console redirection and logging
are process-global. Logging files from the last invocation may stay open until the
next invocation resets logging. Do not leave background jobs writing after an
invocation returns.

A consumer with a runtime-only distribution dependency can resolve this overload
reflectively. Updating only the Maven facade artifacts does not install it into an
older checker JAR. No automatic Scala fallback is provided.

## Verification and module paths

```sh
sbt 'tlair / test' 'tla_ir_java / test' 'tla_io / test' 'tla_io_java / test' 'tool / test'
```

Java unit tests exercise construction, inspection, transformations, type
operations and I/O.

Apalache's automatic module names are `org.apalache_mc.tla.ir`, `.jir`, `.io` and
`.jio`. Some third-party Scala artifacts do not have usable derived module names,
so a fully modular transitive graph is not promised.

No downstream hardening migration or snapshot publication is part of these changes.

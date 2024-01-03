package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import scalaz._

import scala.language.implicitConversions

/**
 * This package defines key types and conversions related to [[ScopedBuilder]].
 *
 * =A brief introduction to [[ScopedBuilder]] development=
 *
 * [[ScopedBuilder]] is a utility class for generating TLA+ IR expressions. It can be conceptually separated into three
 * distinct layers:
 *   1. The signature layer
 *   1. The type-safe, scope-unsafe layer
 *   1. The type-safe, scope-safe layer
 *
 * ==The signature layer==
 *
 * Each TLA+ operator has an associated [[at.forsyte.apalache.tla.lir.oper.TlaOper TlaOper]] operator in the IR. Most
 * operators have type signatures, that is, they restrict the types of arguments allowed to construct valid
 * [[at.forsyte.apalache.tla.lir.OperEx OperEx]] expressions. For instance,
 * [[at.forsyte.apalache.tla.lir.oper.TlaArithOper.plus TlaArithOper.plus]] represents the arithmetic operator `+` and
 * has the signature `(Int, Int) => Int` in the type system, meaning that `e @ OperEx(TlaArithOper.plus, x, y)` is
 * considered valid iff `x`, `y`, and `e` are all tagged with `Typed(IntT1)`. Similarly,
 * [[at.forsyte.apalache.tla.lir.oper.TlaOper.chooseBounded TlaOper.chooseBounded]] has the signature `(t, Set(t), Bool)
 * \=> t`, meaning that an expression`e @ OperEx(TlaOper.chooseBounded, x, S, p)` is considered valid if `x` and `e` are
 * tagged with `Typed(t)`, for some `t`, `S` is tagged with `Typed(SetT1(t))` (for the same `t`), and `p` is tagged with
 * `Typed(BoolT1)`.
 *
 * You can think of a signature `(a1,...,an) => b` as a partial function; given a sequence of argument types `v1, ...
 * vn`, it returns some type `c` (derived from `b`), if the types `v1, ..., vn` match the pattern `a1, ..., an`. More
 * precisely, the return value is `s(b)`, if there exists some type substitution `s`, such that `s(ai) = vi` for all
 * indices `i = 1,...,n`.
 *
 * To reason about signatures, we define two types, [[PartialSignature]] and [[Signature]]. They serve the same purpose,
 * but differ in the way they behave on mis-matches. [[PartialSignature]]s are bare-bones descriptions of the
 * happy-case; given an input pattern `a1,...,an`, they describe the output `b`. For example, `plus` has the
 * [[PartialSignature]]
 * {{{
 *   { case Seq(IntT1, IntT1) => IntT1 }
 * }}}
 * that is, given an input sequence of exactly two arguments, both of which are `IntT1`, it deduces the result type to
 * be `IntT1`. Similarly, `chooseBounded` has the signature
 * {{{
 *   { case Seq(t, SetT1(tt), BoolT1) if t == tt => t }
 * }}}
 * that is, given an input sequence of exactly three arguments, the first two of which are `t` and `Set(t)`, for some
 * `t`, and the last of which is `BoolT1`, it deduces the result type to be `t`. This means that applying this partial
 * signature to `Seq(IntT1, SetT1(IntT1), BoolT1)`, would return `IntT1` while applying it to `Seq(StrT1, SetT1(StrT1),
 * BoolT1)` would return `StrT1`. It is not applicable to `Seq(IntT1, SetT1(StrT1), BoolT1)`.
 *
 * [[Signature]]s complete [[PartialSignature]]s, by equipping them with an exception, to be thrown should the input
 * sequence not match the pattern defined by the corresponding [[PartialSignature]]. This lifting is done by
 * [[BuilderUtil.completePartial completePartial]], if all we want is a total function, or
 * [[BuilderUtil.checkForArityException checkForArityException]], to output a more precise error message, outlining
 * whether [[PartialSignature]] application failed because of the non-existence of a type substitution, or simply
 * because of an invalid arity.
 *
 * [[SignatureMap]] represents a map from [[at.forsyte.apalache.tla.lir.oper.TlaOper TlaOper]]s to their [[Signature]]s
 * (for those that have one). The module [[signatures]] defines [[SignatureMap]]s for various subtypes of
 * [[at.forsyte.apalache.tla.lir.oper.TlaOper TlaOper]], grouped by their category. Each object in [[signatures]]
 * defines a
 * {{{
 *   def getMap: SignatureMap
 * }}}
 * A convenience method [[BuilderUtil.signatureMapEntry signatureMapEntry]] is provided, which creates a
 * [[SignatureMap]] entry from a partial signature and operator. Internally, it invokes
 * [[BuilderUtil.checkForArityException]], by reading the operator's name and arity.
 *
 * `knownSignatures` stores all operator signatures that are considered known to [[ScopedBuilder]].
 *
 * ==The type-safe, scope-unsafe layer==
 *
 * In this layer, we define builder methods, which generate type-safe (though potentially scope-unsafe)
 * [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] values. For the most part, we focus on
 * [[at.forsyte.apalache.tla.lir.OperEx OperEx]] values, as literals can be trivially constructed as type-safe.
 *
 * We solve the following problem: Given [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] arguments `x1,...,xn` and a
 * [[at.forsyte.apalache.tla.lir.oper.TlaOper TlaOper]] argument `oper`, what type, if any, can be assigned to `e @
 * OperEx(oper, x1, ..., xn)`, such that `e` is soundly typed w.r.t. the type signature of the TLA+ operator represented
 * by `oper` in the type system.
 *
 * [[TypeComputation]] describes a solution to the above problem. It is a function that takes a sequence of
 * [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] arguments (`x1, ..., xn`), and returns a [[TypeComputationResult]]:
 * either a type (the type of `e`) or an exception (if `e` cannot be assigned a valid type). Notice that
 * [[TypeComputation]] operates over [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]], and not
 * [[at.forsyte.apalache.tla.lir.TlaType1 TlaType1]]. This is because the types of the expressions `x1,...,xn` are
 * sometimes insufficient to determine the type of `e`. A concrete example: if `r` is a record with the type `{ a: Int,
 * b: Str }`, then the type of `OperEx( TlaFunOper.app, r, x)` depends on whether `x` is the literal `"a"` or the
 * literal `"b"` (not just on whether the type of `x` is `Str`).
 *
 * In most cases it is sufficient to know just the types of `x1, ..., xn`, to determine the type of `e`. We therefore
 * define [[PureTypeComputation]]s as functions from sequences of [[at.forsyte.apalache.tla.lir.TlaType1 TlaType1]]
 * values to [[TypeComputationResult]]s. Note that a [[PureTypeComputation]] naturally defines a [[TypeComputation]] (by
 * only looking at the argument types). This is implemented in the implicit conversion [[fromPure]].
 *
 * How do we obtain these [[TypeComputation]]s, for a given operator?
 *
 * There are two distinct cases:
 *   1. `oper` is associated with some [[Signature]], i.e. `TypeComputationFactory.knownSignatures.contains(oper)`. This
 *      is the case for most operators.
 *   1. `oper` does not have a signature in `knownSignatures`. This is the case for operators such as
 *      [[at.forsyte.apalache.tla.lir.oper.TlaFunOper.app TlaFunOper.app]] or
 *      [[at.forsyte.apalache.tla.lir.oper.ApalacheInternalOper.notSupportedByModelChecker ApalacheInternalOper.notSupportedByModelChecker]]
 *      (and more).
 *
 * Observe that a [[Signature]] is already a [[PureTypeComputation]]. Therefore, any operator with an associated
 * signature has a naturally associated [[TypeComputation]] (obtained by applying [[fromPure]] to the [[Signature]]). In
 * particular, we can access the [[PureTypeComputation]]s via
 * [[TypeComputationFactory.computationFromSignature computationFromSignature]]. For operators, which do not have
 * [[Signature]]s, we need to manually implement these [[TypeComputation]]s on an individual basis.
 *
 * In both cases [[BuilderUtil.composeAndValidateTypes]] performs the composition task for us: given an operator `oper`,
 * a [[TypeComputation]] `cmp` and arguments `args` [[BuilderUtil.composeAndValidateTypes]] computes `cmp(args)`. If it
 * produces an exception, it is thrown, otherwise `OperEx(oper, args:_*)(Typed(t))` is produced, where `t` is the type
 * determined by `cmp(args)`.
 *
 * [[unsafe.ProtoBuilder]] defines the utility method
 * [[unsafe.ProtoBuilder.buildBySignatureLookup buildBySignatureLookup]], which uses
 * [[TypeComputationFactory.computationFromSignature computationFromSignature]] to get the (Pure)[[TypeComputation]]s
 * associated with an operator, then calls [[BuilderUtil.composeAndValidateTypes composeAndValidateTypes]] internally.
 * Thus, is a builder method in [[unsafe]] constructs expressions for an operator `oper`, associated with a
 * [[Signature]], the typical way to implement the method `method(arg1, ..., argN)` is by `buildBySignatureLookup(oper,
 * arg1, ..., argN)`.
 *
 * [[unsafe]] contains collections of builder methods, categorized by the type of IR operator they build
 * ([[at.forsyte.apalache.tla.lir.oper.TlaBoolOper TlaBoolOper]],
 * [[at.forsyte.apalache.tla.lir.oper.TlaArithOper TlaArithOper]],
 * [[at.forsyte.apalache.tla.lir.oper.ApalacheOper ApalacheOper]], etc.)
 *
 * ==The type-safe, scope-safe layer==
 *
 * In practice, it is not enough to construct type-safe expressions (w.r.t. signatures). Consider the following example:
 * `CHOOSE (x: Int) \in (S: Set(Int)): (x: Bool)`. We know `CHOOSE` has the signature `(t, Set(t), Bool) => t`, so from
 * the perspective of type-correctness, the arguments `x: Int`, `S: Set(Int)` and `x: Bool` match the pattern and the
 * constructed expression is considered well-typed (with a result type of `Int`). Notice, however, that the variable `x`
 * is used with two different types in the same expression, once with `Int` in the position of the bound variable, and
 * once with `Bool` in the `CHOOSE` body.
 *
 * Scope safety is defined as the combination of the following properties:
 *   1. Type consistency: Multiple instances of a variable within the same scope have the same type. They may have
 *      different types in different scopes. Example: `(\E x \in {1,2,3}: TRUE) /\ \E x \in {"1", "2", "3"}: TRUE`, is
 *      type- consistent, but `\E x \in {"1", "2", "3"}: x > 0` is not.
 *   1. Absence of shadowing: Bound variable names are unambiguous w.r.t. the location binding them. Example: `\E x \in
 *      A: \E x \in B: x > 0` shadows `x` (it is unclear whether `x` in `x > 0` is bound to `A` or `B`).
 *
 * Type-correctness is a local property; a violation occurs due to an immediate incompatibility between a parent node
 * and its direct children in the IR tree. Unfortunately, scope-safety is not; it could be the case that two
 * expressions, which together violate scope-safety occur in different positions in the IR sub-tree (possibly on
 * parallel sub-trees s.t. one is not an ancestor of the other).
 *
 * Because scope-safety is non-local, builder methods need to keep track of scope ''persistently, and in addition to''
 * constructing a [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] expression. Instead of a mutable `var` storage, or methods
 * which return tuples (and thus don't compose), we solve this problem by using `scalaz.State`. We define our notion of
 * persistently stored information in [[TBuilderContext]]; every builder method has the ability to read from, and write
 * to, some [[TBuilderContext]], to determine whether scope-safety would be violated in the construction of the desired
 * expression.
 *
 * We define the (parameterized) alias [[TBuilderInternalState]]. A [[TBuilderInternalState]][T] value represents the
 * ''process'' of constructing a value of type `T`, while maintaining an internal, persistent [[TBuilderContext]]. Most
 * builder methods construct [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] expressions, so we introduce a shorthand type
 * alias [[TBuilderInstruction]], which is just [[TBuilderInternalState]][`TlaEx`].
 *
 * It is important to note that constructing a [[TBuilderInternalState]] will not throw any kinds of exceptions, even if
 * a scope (or even type) violation would occur, because a [[TBuilderInternalState]] is conceptually a process, not a
 * value. To actually obtain a value (or possibly an exception), we can invoke one of two methods: [[build]], or
 * [[BuildViaMethod.build]]. The method (resp. the class) are `implicit`, so they need not be invoked manually. This
 * lets us use [[TBuilderInternalState]][`T`] anywhere we would otherwise need a value of type `T`. For example, given a
 * value `bi: TBuilderInternalState`, we can obtain the `TlaEx` (the construction of which is described by the process
 * `bi`) in any of the following equivalent ways:
 * {{{
 *   val tlaEx: TlaEx = bi
 *   val tlaEx = build(bi)
 *   val tlaEx = bi.build
 * }}}
 * [[liftBuildToSeq]] serves a similar purpose, it implicitly converts a sequence of [[TBuilderInternalState]][`T`] of
 * `T` values.
 *
 * Note to developers: We need to be careful when using methods which accept arguments of `Any` type (e.g. `==`). In
 * those cases, [[build]], or [[BuildViaMethod.build]] must be explicitly invoked, as matching `Any` will not trigger an
 * implicit call to [[build]].
 *
 * What is left is to determine how to combine this approach with the scope-unsafe-layer builder methods in [[unsafe]],
 * which already guarantee type-safety. Each builder in [[unsafe]] has a corresponding scope-safe builder in
 * [[subbuilder]], following the same grouping strategy (by [[at.forsyte.apalache.tla.lir.oper.TlaOper TlaOper]] sort).
 *
 * For every scope-safe method `method` there is a 2nd-layer method `method(arg1: TlaEx, ..., argN: TlaEx): TlaEx`
 * defined in some `unsafeBuilder` used as a basis (a few methods take arguments, which are not `TlaEx`, we omit them
 * here). Then, the scope-safe `method` has the signature `method(arg1: TBuilderInstruction, ..., argN:
 * TBuilderInstruction): TBuilderInstruction`. This way, it composes nicely with other scope-safe methods. The general
 * implementation of a scope-safe method from a scope-unsafe method is fairly simple:
 * {{{
 *   for {
 *     arg1Ex <- arg1
 *     ...
 *     argNEx <- argN
 *   } yield unsafeBuilder.method(arg1Ex, ..., argNEx)
 * }}}
 * This way, we get the type-correctness from the 2nd layer for free. [[BuilderUtil]] defines convenience methods for
 * this generic construction: [[BuilderUtil.binaryFromUnsafe binaryFromUnsafe]], and [[BuilderUtil.ternaryFromUnsafe]]
 * (the unary case is just a `map`).
 *
 * The exceptions to this general rule are the [[subbuilder.LiteralAndNameBuilder.name name]] method, which introduces a
 * variable with a given name and type, and the various methods, which introduce bound variables (e.g. `exists`,
 * [[subbuilder.FunBuilder.funDef funDef]], `choose`, etc.). These methods manipulate (or read) the internal
 * [[TBuilderContext]], to ensure scope-safety. The latter utilize the convenience methods
 * [[BuilderUtil.boundVarIntroductionBinary boundVarIntroductionBinary]],
 * [[BuilderUtil.boundVarIntroductionTernary boundVarIntroductionTernary]], and
 * [[BuilderUtil.boundVarIntroductionVariadic boundVarIntroductionVariadic]] to handle bound-variable-introduction,
 * which internally uses [[BuilderUtil.markAsBound markAsBound]], [[BuilderUtil.getAllBound getAllBound]], and
 * [[BuilderUtil.getAllUsed getAllUsed]].
 *
 * [[ScopedBuilder]] is the amalgamation of all the builder methods defined in [[subbuilder]] (as well as a handful of
 * methods, which construct [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] expressions unrelated to
 * [[at.forsyte.apalache.tla.lir.oper TlaOper]], such as [[ScopedBuilder.decl decl]] or `letIn`). The package `types`
 * offers a premade instance of [[ScopedBuilder]] and is recommended to be used whenever one needs to construct type-
 * and scope-safe TLA+ expressions.
 *
 * @author
 *   Jure Kukovec
 */
package object typecomp {

  /**
   * Build a data structure (e.g., `TlaEx` or `TlaOperDecl`), given a state of the builder.
   *
   * @param builderState
   *   the internal state of the builder, which captures a data structure made so far
   * @tparam T
   *   the type of a data structure to build, e.g., `TlaEx` or `TlaOperDecl`.
   * @return
   *   the constructed data structure of type `T`
   * @throws TBuilderTypeException
   *   when a constructed expression is ill-typed
   * @throws TBuilderScopeException
   *   when a constructed expression has an incorrect scope
   */
  implicit def build[T](builderState: TBuilderInternalState[T]): T = builderState.run(TBuilderContext.empty)._2

  /**
   * An implicit conversion via a class that works as [[build]], but via a method call to `.build()`.
   *
   * @param builderState
   *   the internal state of the builder, which captures a data structure made so far
   * @tparam T
   *   the type of a data structure to build, e.g., `TlaEx` or `TlaOperDecl`.
   */
  implicit class BuildViaMethod[T](builderState: TBuilderInternalState[T]) {

    /**
     * Build a data structure (e.g., `TlaEx` or `TlaOperDecl`) from the left-hand side.
     *
     * @return
     *   the constructed data structure of type `T`
     * @throws TBuilderTypeException
     *   when a constructed expression is ill-typed
     * @throws TBuilderScopeException
     *   when a constructed expression has an incorrect scope
     */
    def build: T = builderState
  }

  /**
   * Apply the `build` method to a sequence.
   *
   * @param builderStates
   *   a sequence of [[TBuilderInternalState]]
   * @tparam T
   *   the type of a data structure to build, e.g., `TlaEx` or `TlaOperDecl`.
   * @return
   *   the sequence of constructed data structures of type `T`
   * @throws TBuilderTypeException
   *   when a constructed expression is ill-typed
   * @throws TBuilderScopeException
   *   when a constructed expression has an incorrect scope
   */
  implicit def liftBuildToSeq[T](builderStates: Seq[TBuilderInternalState[T]]): Seq[T] =
    builderStates.map(build)

  // Builder-thrown exceptions

  /** Thrown if a TypeComputation finds fault with types */
  class TBuilderTypeException(message: String) extends Exception(message)

  /** Thrown if scope validation finds a clash between multiple instances of the same variable name */
  class TBuilderScopeException(message: String) extends Exception(message)

  /** Type computations return types or TypeExceptions */
  type TypeComputationResult = Either[TBuilderTypeException, TlaType1]

  /** Builder methods return TlaEx (they throw exceptions) */
  type TBuilderResult = TlaEx

  /**
   * A type computation returns the result type of an operator application, given the concrete arguments. In general,
   * argument types are not enough, because we need concrete fields/indices for records/sequences.
   */
  type TypeComputation = Seq[TlaEx] => TypeComputationResult

  /**
   * For most operators, we don't need the exact values (just types) of the arguments to determine the result type. Pure
   * computations are TypeComputations that are associated with such operators.
   */
  type PureTypeComputation = Seq[TlaType1] => TypeComputationResult

  /**
   * TBuilderContext holds all of the information about the internal state of the builder. It can be extended in the
   * future, to have the builder perform additional static analysis, e.g. assignment analysis.
   *
   *   - `freeNameScope` tracks the variables currently considered as free and their types.
   *   - `usedNames` tracks the set of free and bound names in the scope.
   *
   * We track both to prevent shadowing. Expressions which introduce bound variables, e.g. \E x \in S: P, may cause
   * shadowing if:
   *   - `x` appears as bound in `P` (e.g. \E x \in S: \E x \in T: x).
   *   - `x` appears as free or bound in `S` (e.g. \E x \in {x}: P(x))
   *
   * Invariant: freeNameScope.keys \subseteq usedNames
   */
  final case class TBuilderContext(freeNameScope: Map[String, TlaType1], usedNames: Set[String])
  object TBuilderContext {
    def empty: TBuilderContext = TBuilderContext(Map.empty, Set.empty)
  }

  /** An IntenalState is a computation (possibly) mutating some MetaInfo */
  type TBuilderInternalState[T] = State[TBuilderContext, T]

  /** Builder methods generate `TBuilderInstruction`s, which construct TBuilderResult values on demand */
  type TBuilderInstruction = TBuilderInternalState[TBuilderResult]

  /** Some builder methods generate TlaOperDecl instead of `TBuilderResult` */
  type TBuilderOperDeclInstruction = TBuilderInternalState[TlaOperDecl]

  // Each PureTypeComputation naturally defines a TypeComputation by first mapping fromTypeTag over the args
  implicit def fromPure(cmp: PureTypeComputation): TypeComputation = { args =>
    cmp(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) })
  }

  // convenience implicit, so we can avoid typing Right
  implicit def liftRet(tt: TlaType1): TypeComputationResult = Right(tt)

  /**
   * A signature, if it exists, is as a function from domain types to either a codomain type or an exception (i.e. a
   * [[PureTypeComputation]]).
   */
  type Signature = PureTypeComputation

  /** A signature that is defined as a partial function. */
  type PartialSignature = PartialFunction[Seq[TlaType1], TypeComputationResult]

  /** Maps operators to their associated signature generators. */
  type SignatureMap = Map[TlaOper, Signature]
}

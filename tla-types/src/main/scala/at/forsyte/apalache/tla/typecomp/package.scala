package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.SignatureMap
import scalaz._

import scala.language.implicitConversions

/**
 * This package defines key types and conversions related to [[ScopedBuilder]].
 *
 * <h1> A brief introduction to [[ScopedBuilder]] <h1>
 *
 * [[ScopedBuilder]] is a utility class for generating TLA+ IR expressions. It can be conceptually separated into three
 * distinct layers:
 *   1. The signature layer
 *   1. The type-safe, scope-unsafe layer
 *   1. The type-safe, scope-safe layer
 *
 * <h2> The signature layer <h2>
 *
 * Each TLA+ operator has an associated [[TlaOper]] operator in the IR. The majority (but not all) of the operators have
 * type signatures, that is, they restrict the types of the arguments, that may be used to construct valid [[OperEx]]
 * expressions. For instance, [[at.forsyte.apalache.tla.lir.oper.TlaArithOper.plus]] represents the arithmetic operator
 * `+` and has the signature `(Int, Int) => Int` in the type system, meaning that `e@OperEx(TlaArithOper.plus, x, y)` is
 * considered valid iff both `x`, `y`, and `e` are all tagged with `Typed(IntT1)`. Similarly,
 * [[at.forsyte.apalache.tla.lir.oper.TlaOper.chooseBounded]] has the signature `(t, Set(t), Bool) => t`, meaning that
 * `e@OperEx(TlaOper.chooseBounded, x, S, p)` is considered valid if `x` and `e` are tagged with `Typed(t: TlaType1)`,
 * for some `t`, `S` is tagged with `Typed(SetT1(t))` (for the same `t`), and `p` is tagged with `Typed(BoolT1)`.
 *
 * You can think of a signature `(a1,...,an) => b` as a partial function; given a sequence of argument types `v1, ...
 * vn`, it returns some type `c` (derived from `b`), if the types `v1, ..., vn` match the pattern `a1, ..., an`. More
 * precisely, the return value is `s(b)`, if there exists some type substitution `s`, such that `s(ai) = vi` for all i.
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
 * `t`, and the last of which is `BoolT1, , it deduces the result type to be `t`. This means that applying this partial
 * signature to `Seq(IntT1, SetT1(IntT1), BoolT1)`, would return `IntT1` while applying it to `Seq(StrT1, SetT1(StrT1),
 * BoolT1)` would return `StrT1`. It is not applicable to `Seq(IntT1, SetT1(StrT1), BoolT1)`.
 *
 * [[Signature]]s complete [[PartialSignature]]s, by equipping them with an exception message, should the input sequence
 * not match the pattern defined by the [[PartialSignature]]. This lifting is done by [[BuilderUtil.completePartial]],
 * which can be further refined by [[BuilderUtil.checkForArityException]], to output a more precise error message,
 * outlining whether [[PartialSignature]] application failed because of the non-existence of a type substitution, or
 * simply because of an invalid arity.
 *
 * [[SignatureMap]] represents a map from [[at.forsyte.apalache.tla.lir.oper.ApalacheOper]]s to their signatures (for
 * those that have one). The module [[signatures]] defines maps for various subtypes of
 * [[at.forsyte.apalache.tla.lir.oper.ApalacheOper]], grouped by their category. A convenience method
 * [[BuilderUtil.signatureMapEntry]] is provided, which creates a [[SignatureMap]] entry from a partial signature and
 * operator. Internally, it invokes [[BuilderUtil.checkForArityException]], by reading the operator's name and arity.
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

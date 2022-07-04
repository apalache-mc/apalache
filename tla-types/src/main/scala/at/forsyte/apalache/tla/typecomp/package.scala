package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import scalaz._

import scala.language.implicitConversions

/**
 * The key definitions related to the typed builder. The most important ones for the users of this API are the methods:
 *
 *   - an implicit conversion `build` that converts a builder state to its final form, e.g., to `TlaEx`.
 *   - an implicit conversion `liftBuildToSeq` that applies `build` to a sequence.
 *
 * To use the above methods in your code, import the implicit conversions as follows:
 *
 * {{{
 *  import at.forsyte.apalache.tla.typecomp._
 * }}}
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
    def build: T = {
      builderState.run(TBuilderContext.empty)._2
    }
  }

  /**
   * Apply the `build` method to a sequence.
   *
   * @param builderStates
   *   a sequence of
   * @tparam T
   *   the type of a data structure to build, e.g., `TlaEx` or `TlaOperDecl`.
   * @return
   *   the sequence of constructed data structured of type `T`
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

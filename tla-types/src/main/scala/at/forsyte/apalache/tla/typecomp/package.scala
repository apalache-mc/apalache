package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir._

import scala.language.implicitConversions
import scalaz._

// Contains classes, typedefs and implicit conversion methods used in the package
package object typecomp {

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
   * `nameScope` tracks the types of the variables currently considered as free.
   */
  final case class TBuilderContext(nameScope: Map[String, TlaType1])
  object TBuilderContext {
    def empty: TBuilderContext = TBuilderContext(Map.empty)
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

  // Allows for the seamless conversion of -Instruction expressions to TlaEx, when the latter is required
  implicit def build[T](wrap: TBuilderInternalState[T]): T = wrap.run(TBuilderContext.empty)._2
  implicit def liftBuildToSeq[T](wrapCollection: Seq[TBuilderInternalState[T]]): Seq[T] =
    wrapCollection.map(build)

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

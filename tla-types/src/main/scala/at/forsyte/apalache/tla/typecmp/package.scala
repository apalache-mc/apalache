package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperT1, TlaEx, TlaType1, ValEx}

import scala.language.implicitConversions
import scalaz._

// Contains classes, typedefs and implicit conversion methods used in the package
package object typecmp {

  // Builder-thrown exceptions
  /** Thrown if a TypeComputation finds fault with types */
  class BuilderTypeException(message: String) extends Exception(message)

  /** Thrown if scope validation finds a clash between multiple instances of the same variable name */
  class BuilderScopeException(message: String) extends Exception(message)

  /** Type computations return types or TypeExceptions */
  type TypeComputationReturn = Either[BuilderTypeException, TlaType1]

  /** Builder methods return TlaEx (they throw exceptions) */
  type BuilderReturn = TlaEx

  /**
   * A type computation returns the result type of an operator application, given the concrete arguments. In general,
   * argument types are not enough, because we need concrete fields/indices for records/sequences.
   */
  type TypeComputation = Seq[TlaEx] => TypeComputationReturn

  /**
   * For some (most) operators, we don't need the exact values (just types) of the arguments to determine the result
   * type. Pure computations are TypeComputations that are associated with such operators.
   */
  type PureTypeComputation = Seq[TlaType1] => TypeComputationReturn

  /**
   * MetaInfo holds all of the information about the internal state of the builder. For now, this just includes the name
   * scope, but it can be extended in the future, to have the builder perform additional static analysis, e.g.
   * assignment analysis.
   *
   * `nameScope` tracks the types of the variables currently considered as free
   */
  final case class MetaInfo(nameScope: Map[String, TlaType1])

  /** An IntenalState is a computation (possibly) mutating some MetaInfo */
  type InternalState[T] = State[MetaInfo, T]

  /** Builders operate over BuilderWrappers, which hold MetaInfo as state */
  type BuilderWrapper = InternalState[BuilderReturn]

  // Special wrapper cases for subclasses of TlaEx
  /** Variant of BuilderWrapper, when the built expression must be NameEx */
  type NameWrapper = InternalState[NameEx]

  /** Variant of BuilderWrapper, when the built expression must be ValEx */
  type ValWrapper = InternalState[ValEx]

  // Because State[_,A] is invariant in A, InternalState[NameEx] <: InternalState[TlaEx] does not hold
  // We can fix this discrepancy with an implicit that upcasts NameEx/ValEx to TlaEx
  implicit def generalizeWrapperN(nw: NameWrapper): BuilderWrapper = nw.map(_.asInstanceOf[TlaEx])
  implicit def generalizeWrapperV(vw: ValWrapper): BuilderWrapper = vw.map(_.asInstanceOf[TlaEx])

  // Each PureTypeComputation naturally defines a TypeComputation by first mapping fromTypeTag over the args
  implicit def fromPure(cmp: PureTypeComputation): TypeComputation = { args =>
    cmp(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) })
  }

  // convenience implicit, so we can avoid typing Right
  implicit def liftRet(tt: TlaType1): TypeComputationReturn = Right(tt)

  // Allows for the seamless conversion of BuilderWrapper expressions to TlaEx, when the latter is required
  implicit def build[T](wrap: InternalState[T]): T = wrap.run(MetaInfo(Map.empty))._2
  implicit def buildSeq[T](wrapCollection: Seq[InternalState[T]]): Seq[T] =
    wrapCollection.map(build)

  // Since some operators are polyadic, we parameterize signatures for the same operator by the # or arguments */
  /** A signature, if it exists, is an operator type */
  type Signature = OperT1

  /**
   * Given an arity hint `n`, returns an arity-aware signature sig: Signature. `sig.from.size` need not equal `n`,
   * unless the associated operator is polyadic.
   */
  type SignatureGenerator = Int => OperT1

  /** Maps operators to their associated signature generators. */
  type SignatureGenMap = Map[TlaOper, SignatureGenerator]

  // Implicit lifting, for fixed-arity operators
  implicit def liftOper(operT1: OperT1): SignatureGenerator = _ => operT1
}

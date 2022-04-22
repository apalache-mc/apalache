package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperT1, TlaEx, TlaType1, ValEx}

import scala.language.implicitConversions
import scalaz._

// Contains classes, typedefs and implicit conversion methods used in the package
package object typecmp {

  // Builder-thrown exceptions
  // a typeComputation finds fault with types
  class BuilderTypeException(message: String) extends Exception(message)
  // scope validation finds a clash between multiple instances of the same variable name
  class BuilderScopeException(message: String) extends Exception(message)

  // Type computations return types or TypeExceptions
  type typeComputationReturn = Either[BuilderTypeException, TlaType1]

  // Builder methods return TlaEx (they throw exceptions)
  type builderReturn = TlaEx

  // A type computation returns the result type of an operator application, given the concrete arguments
  // In general, argument types are not enough, because we need concrete fields/indices for records/sequences
  type typeComputation = Seq[TlaEx] => typeComputationReturn
  // For some (most) operators, we don't need the exact values (just types) of the arguments to determine the result type
  // Pure computations are typeComputations that are associated with such operators
  type pureTypeComputation = Seq[TlaType1] => typeComputationReturn

  // MetaInfo holds all of the information held in the internal state of the builder. For now,
  // this just includes the name scope, but it can be extended in the future, to have the builder perform
  // additional static analysis.
  // nameScope tracks the types of the variables currently considered as free
  sealed case class MetaInfo(nameScope: Map[String, TlaType1])

  // Builders operate over BuilderWrappers, which hold MetaInfo as state
  type InternalState[T] = State[MetaInfo, T]
  type BuilderWrapper = InternalState[builderReturn]

  // Special wrapper cases for subclasses of TlaEx
  type NameWrapper = InternalState[NameEx]
  type ValWrapper = InternalState[ValEx]

  // Because State[_,A] is invariant in A, InternalState[NameEx] <: InternalState[TlaEx] does not hold
  // we can fix this discrepancy with an implicit that upcasts NameEx/ValEx to TlaEx
  implicit def generalizeWrapperN(nw: NameWrapper): BuilderWrapper = nw.map(_.asInstanceOf[TlaEx])
  implicit def generalizeWrapperV(vw: ValWrapper): BuilderWrapper = vw.map(_.asInstanceOf[TlaEx])

  // Each pureTypeComputation naturally defines a typeComputation by first mapping fromTypeTag over the args
  implicit def fromPure(cmp: pureTypeComputation): typeComputation = { args =>
    cmp(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) })
  }

  // convenience implicit, so we can avoid typing Right
  implicit def liftRet(tt: TlaType1): typeComputationReturn = Right(tt)

  // Allows for the seamless conversion of BuilderWrapper expressions to TlaEx, when the latter is required
  implicit def build[T](wrap: InternalState[T]): T = wrap.run(MetaInfo(Map.empty))._2

  // Since some operators are polyadic, we parameterize signatures for the same operator by the # or arguments
  type SignatureMap = Map[TlaOper, Int => OperT1]

  // Implicit lifting, for monotyped, fixed-arity operators
  implicit def liftOper(operT1: OperT1): Int => OperT1 = _ => operT1
}

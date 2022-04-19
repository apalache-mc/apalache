package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{TlaEx, TlaType1}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier}
import scala.language.implicitConversions

import scalaz._

package object typecmp {

  class BuilderTypeException(message: String) extends Exception(message)
  class BuilderScopeException(message: String) extends Exception(message)

  type typeComputationReturn = Either[BuilderTypeException, TlaType1]
  type builderReturn = TlaEx

  type typeComputation = Seq[TlaEx] => typeComputationReturn
  type pureTypeComputation = Seq[TlaType1] => typeComputationReturn

  sealed case class MetaInfo(nameScope: Map[String, TlaType1])

  type InternalState[T] = State[MetaInfo, T]
  type BuilderWrapper = InternalState[builderReturn]

  implicit def fromPure(cmp: pureTypeComputation): typeComputation = { args =>
    cmp(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) })
  }

  implicit def liftRet(tt: TlaType1): typeComputationReturn = Right(tt)

  implicit def build(wrap: BuilderWrapper): builderReturn = wrap.run(MetaInfo(Map.empty))._2

  // Performs unificaiton on 2 types with a fresh unifier
  def singleUnification(
      lhs: TlaType1,
      rhs: TlaType1,
      subst: Substitution = Substitution.empty): Option[(Substitution, TlaType1)] = {
    (new TypeUnifier).unify(subst, lhs, rhs)
  }
}

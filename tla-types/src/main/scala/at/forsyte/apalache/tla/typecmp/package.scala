package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{TlaEx, TlaType1}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier}
import scala.language.implicitConversions

package object typecmp {

  class TypedBuilderException(message: String) extends Exception(message)

  type typeComputationReturn = Either[TypedBuilderException, TlaType1]
  type typeComputation = Seq[TlaEx] => typeComputationReturn
  type pureTypeComputation = Seq[TlaType1] => typeComputationReturn

  implicit def fromPure(cmp: pureTypeComputation): typeComputation = { args =>
    cmp(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) })
  }

  implicit def liftRet(tt: TlaType1): typeComputationReturn = Right(tt)

  def throwMsg(msg: String): typeComputationReturn = Left(new TypedBuilderException(msg))

  // Performs unificaiton on 2 types with a fresh unifier
  def singleUnification(
      lhs: TlaType1,
      rhs: TlaType1,
      subst: Substitution = Substitution.empty): Option[(Substitution, TlaType1)] = {
    (new TypeUnifier).unify(subst, lhs, rhs)
  }
}

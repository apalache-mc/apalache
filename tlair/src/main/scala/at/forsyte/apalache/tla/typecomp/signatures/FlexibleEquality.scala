package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.TlaType1

import at.forsyte.apalache.tla.types.TypeUnifier
import at.forsyte.apalache.tla.types.TypeVarPool
import at.forsyte.apalache.tla.types.Substitution

/**
 * Determines flexible equality ([[compatible]]), i.e. an equivalence relation over TT1, which is equality for
 * non-record types, but allows the comparison of records types with compatible fields
 *
 * @author
 *   Jure Kukovec, ShonFeder
 */
object FlexibleEquality {

  // None if no common supertype, Some(e) if compatible, and the common supertype is e.
  def commonSupertype(lhs: TlaType1, rhs: TlaType1): Option[TlaType1] = {
    // TypeUnifier is not threadsafe, and creating a new instance
    // for each invocation prevents race conditions in the tests
    val typeUnifier = new TypeUnifier(new TypeVarPool())
    typeUnifier.unify(Substitution.empty, lhs, rhs).map(_._2)
  }

  def commonSeqSupertype(seq: Seq[TlaType1]): Option[TlaType1] =
    seq.headOption.flatMap { h =>
      seq.foldLeft(Option(h)) { case (tOpt, elem) =>
        for {
          t <- tOpt
          superT <- commonSupertype(t, elem)
        } yield superT
      }
    }

  def compatible(lhs: TlaType1, rhs: TlaType1): Boolean = commonSupertype(lhs, rhs).nonEmpty
}

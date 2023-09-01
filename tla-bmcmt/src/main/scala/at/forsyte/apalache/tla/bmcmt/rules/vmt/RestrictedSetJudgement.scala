package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet, TlaNatSet, TlaPredefSet}

/**
 * RestrictedSetJudgement is used to evaluate sets permitted in the reTLA fragment (i.e. restricted sets).
 *
 * Restricted sets are Int, Nat, BOOLEAN and any CONSTANT values typed Set(_). `constNames` is assumed to only contain
 * the names of the CONSTANTs with set types.
 *
 * @author
 *   Jure Kukovec
 */
class RestrictedSetJudgement(constSets: Map[String, UninterpretedSort]) {
  def isRestrictedSet(ex: TlaEx): Boolean =
    ex match {
      case ValEx(s: TlaPredefSet) =>
        s match {
          case TlaIntSet | TlaNatSet | TlaBoolSet => true
          case _                                  => false
        }
      case NameEx(name) => constSets.contains(name)
      case _            => false
    }

  // Assumption: isRestrictedSet
  def getSort(ex: TlaEx): Sort =
    ex match {
      case ValEx(s: TlaPredefSet) =>
        s match {
          case TlaIntSet | TlaNatSet => IntSort
          case TlaBoolSet            => BoolSort
          case _                     => throw new RewriterException(s"$s not supported in reTLA", ex)
        }
      case NameEx(name) if constSets.contains(name) => constSets(name)
      case _                                        => throw new RewriterException("Cannot determine sort of set", ex)
    }
}

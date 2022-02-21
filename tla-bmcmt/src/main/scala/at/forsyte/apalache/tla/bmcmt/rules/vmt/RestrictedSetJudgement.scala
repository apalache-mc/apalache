package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.UninterpretedSort
import at.forsyte.apalache.tla.lir.formulas.{Sort, StandardSorts}
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet, TlaNatSet, TlaPredefSet}

// Restricted sets are Int, Nat, BOOLEAN and any CONSTANT values typed Set(_)
// constNames is assumed to only contain the names of the CONSTANTs, who have set types
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
          case TlaIntSet | TlaNatSet => StandardSorts.IntSort()
          case TlaBoolSet            => StandardSorts.BoolSort()
          case _                     => throw new RewriterException(s"$s not supported in reTLA", ex)
        }
      case NameEx(name) if constSets.contains(name) => constSets(name)
      case _                                        => throw new RewriterException("Cannot determine sort of set", ex)
    }
}

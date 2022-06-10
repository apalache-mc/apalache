package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet, TlaNatSet, TlaPredefSet}

/**
 * RestrictedSetJudgement is used to evaluate sets permitted in the reTLA fragment (i.e. restricted sets).
 *
 * Restricted sets are Int, Nat, BOOLEAN and any CONSTANT values typed Set(_) (primitive), as well ass function sets of
 * the form [S -> T], where S and T are non-function restricted sets. `constNames` is assumed to only contain the names
 * of the CONSTANTs with set types.
 *
 * @author
 *   Jure Kukovec
 */
class RestrictedSetJudgement(constSets: Map[String, UninterpretedSort], intsAsOrderedUninterpreted: Boolean = true) {
  def isPrimitiveRestrictedSet(ex: TlaEx): Boolean =
    ex match {
      case ValEx(s: TlaPredefSet) =>
        s match {
          case TlaIntSet | TlaNatSet | TlaBoolSet => true
          case _                                  => false
        }
      case NameEx(name) => constSets.contains(name)
      case _            => false
    }

  def isRestrictedSet(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaSetOper.funSet, dom, cdm) =>
        isPrimitiveRestrictedSet(cdm) && (dom match {
          case OperEx(TlaSetOper.times, sets @ _*) => sets.forall(isPrimitiveRestrictedSet)
          case _                                   => isPrimitiveRestrictedSet(dom)
        })
      case _ => isPrimitiveRestrictedSet(ex)
    }

  // Assumption: isRestrictedSet
  private def getPrimitiveSort(ex: TlaEx): Sort =
    ex match {
      case ValEx(s: TlaPredefSet) =>
        s match {
          case TlaIntSet | TlaNatSet => if (intsAsOrderedUninterpreted) Sort.intOrderSort else IntSort()
          case TlaBoolSet            => BoolSort()
          case _                     => throw new RewriterException(s"$s not supported in reTLA", ex)
        }
      case NameEx(name) if constSets.contains(name) => constSets(name)
      case _                                        => throw new RewriterException("Cannot determine sort of set", ex)
    }

  // Assumption: isRestrictedSet
  def getSort(ex: TlaEx): Sort =
    ex match {
      case OperEx(TlaSetOper.funSet, dom, cdm) =>
        val cdmSort = getPrimitiveSort(cdm)
        val domSorts = dom match {
          case OperEx(TlaSetOper.times, sets @ _*) => sets.map(getPrimitiveSort)
          case _                                   => Seq(getPrimitiveSort(dom))
        }
        FunctionSort(cdmSort, domSorts: _*)
      case _ => getPrimitiveSort(ex)
    }
}

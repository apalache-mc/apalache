package at.forsyte.apalache.tla.bmcmt.rewriter

import at.forsyte.apalache.tla.bmcmt.Arena
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.pp.ConstSimplifierBase

/**
 * <p>A simplifier of constant TLA+ expressions, e.g., rewriting 1 + 2 to 3.
 * This simplifier is using some knowledge about SMT.</p>
 *
 * <p>Bugfix #450: make sure that the integers are simplified with BigInt.</p>
 *
 * @author Igor Konnov
 */
class ConstSimplifierForSmt extends ConstSimplifierBase {
  def isFalseConst(ex: TlaEx): Boolean = {
    ex match {
      case ValEx(TlaBool(false)) => true
      case NameEx(name)          => name == Arena.falseName
      case _                     => false
    }
  }

  def isTrueConst(ex: TlaEx): Boolean = {
    ex match {
      case ValEx(TlaBool(true)) => true
      case NameEx(name)         => name == Arena.trueName
      case _                    => false
    }
  }

  def isBoolConst(ex: TlaEx): Boolean = isFalseConst(ex) || isTrueConst(ex)

  /**
   * A shallow simplification that does not recurse into the expression structure.
   */
  override def simplifyShallow: TlaEx => TlaEx = {
    // Here we only do SMT-specific simplifications. The general simplifications are done in the parent.

    case ex @ (NameEx(_) | ValEx(_)) =>
      if (isFalseConst(ex)) {
        ValEx(TlaBool(false))(ex.typeTag)
      } else if (isTrueConst(ex)) {
        ValEx(TlaBool(true))(ex.typeTag)
      } else {
        ex
      }

    // do not go in tla.in and tla.notin, as it breaks down our SMT encoding
    case ex @ (OperEx(TlaSetOper.in, _*) | OperEx(TlaSetOper.notin, _*) | OperEx(BmcOper.withType, _*)) =>
      ex

    // using isTrueConst and isFalseConst that are more precise than those of ConstSimplifierBase

    case OperEx(TlaControlOper.ifThenElse, pred, thenEx, _) if isTrueConst(pred) =>
      thenEx

    case OperEx(TlaControlOper.ifThenElse, pred, _, elseEx) if isFalseConst(pred) =>
      elseEx

    // default
    case ex =>
      super.simplifyShallow(ex)
  }

}

package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{
  LanguageWatchdog,
  TlaExTransformation,
  TransformationTracker
}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}

import scala.annotation.tailrec

/**
  * A simplifier of constant TLA+ expressions, e.g., rewriting 1 + 2 to 3.
  *
  * @author Igor Konnov
  */
class ConstSimplifier(tracker: TransformationTracker)
    extends ConstSimplifierBase
    with TlaExTransformation {
  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    simplify(expr)
  }

  def simplify(rootExpr: TlaEx): TlaEx = {
    rewriteDeep(rootExpr)
  }

  private def rewriteDeep: TlaExTransformation = tracker.track {
    case ex @ ValEx(_) => ex

    case ex @ NameEx(_) => ex

    case OperEx(oper, args @ _*) =>
      simplifyShallow(OperEx(oper, args map rewriteDeep: _*))

    case LetInEx(body, defs @ _*) =>
      val newDefs = defs.map { d =>
        TlaOperDecl(d.name, d.formalParams, simplify(d.body))
      }
      LetInEx(simplify(body), newDefs: _*)

    case ex => ex
  }

  override def simplifyShallow: TlaEx => TlaEx = {
    // boolean operations

    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.notin, lhs, rhs)) =>
      OperEx(TlaSetOper.in, lhs, rhs)

    // default
    case ex =>
      super.simplifyShallow(ex)
  }
}

object ConstSimplifier {
  def apply(tracker: TransformationTracker): ConstSimplifier =
    new ConstSimplifier(tracker)
}

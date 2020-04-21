package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}

/**
  * A simplifier of constant TLA+ expressions, e.g., rewriting 1 + 2 to 3.
  *
  * @author Igor Konnov
  */
class ConstSimplifier(tracker: TransformationTracker) extends TlaExTransformation {
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
      simplifyShallow(OperEx(oper, args map rewriteDeep :_*))

    case LetInEx(body, defs @ _*) =>
      val newDefs = defs.map {
        d => TlaOperDecl(d.name, d.formalParams, simplify(d.body))
      }
      LetInEx(simplify(body), newDefs :_*)

    case ex => ex
  }

  private def simplifyShallow(ex: TlaEx): TlaEx = ex match {
    case ValEx(_) => ex

    case NameEx(_) => ex

    // integer operations
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left + right))

    case OperEx(TlaArithOper.minus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left - right))

    case OperEx(TlaArithOper.minus, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaInt(0)) else ex // this actually happens

    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left * right))

    case OperEx(TlaArithOper.div, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left / right))

    case OperEx(TlaArithOper.mod, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left % right))

    case OperEx(TlaArithOper.exp, ValEx(TlaInt(base)), ValEx(TlaInt(power))) =>
      ValEx(TlaInt(Math.pow(base.toDouble, power.toDouble).toInt))

    case OperEx(TlaArithOper.uminus, ValEx(TlaInt(value))) =>
      ValEx(TlaInt(-value))

    case OperEx(TlaArithOper.lt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left < right))

    case OperEx(TlaArithOper.le, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left <= right))

    case OperEx(TlaArithOper.gt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left > right))

    case OperEx(TlaArithOper.ge, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left >= right))

    case OperEx(TlaOper.eq, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left == right))

    case OperEx(TlaOper.eq, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaBool(true)) else ex

    case OperEx(TlaOper.ne, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left != right))

    case OperEx(TlaOper.ne, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaBool(false)) else ex

    // boolean operations
    case OperEx(TlaBoolOper.and, args @ _*) if args.contains(ValEx(TlaBool(false))) =>
      ValEx(TlaBool(false))

    case OperEx(TlaBoolOper.and, args @ _*) if args.forall (_.isInstanceOf[ValEx]) =>
      val result = !args.contains(ValEx(TlaBool(false)))
      ValEx(TlaBool(result))

    case OperEx(TlaBoolOper.and, args @ _*)  =>
      val simpEx = OperEx(TlaBoolOper.and, args.filterNot { _ == ValEx(TlaBool(true)) } :_*)
      simpEx match {
        case OperEx(TlaBoolOper.and) => ValEx(TlaBool(true)) // an empty disjunction is true
        case e => e
      }

    case OperEx(TlaBoolOper.or, args @ _*) if args.contains(ValEx(TlaBool(true))) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.or, args @ _*) if args.forall (_.isInstanceOf[ValEx]) =>
      val result = args.contains(ValEx(TlaBool(true)))
      ValEx(TlaBool(result))

    case OperEx(TlaBoolOper.or, args @ _*)  =>
      val simpEx = OperEx(TlaBoolOper.or, args.filterNot { _ == ValEx(TlaBool(false)) } :_*)
      simpEx match {
        case OperEx(TlaBoolOper.or) => ValEx(TlaBool(false)) // an empty disjunction is false
        case e => e
      }

    case OperEx(TlaBoolOper.not, ValEx(TlaBool(b))) =>
      ValEx(TlaBool(!b))

    case OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, underDoubleNegation)) =>
      underDoubleNegation

    case OperEx(TlaBoolOper.not, OperEx(TlaOper.ne, lhs, rhs)) =>
      OperEx(TlaOper.eq, lhs, rhs)

//      Keep unmodified, as KerA+ does not allow for /=
//    case OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, lhs, rhs)) =>
//      OperEx(TlaOper.ne, lhs, rhs)

    //      Keep unmodified, as KerA+ does not allow for \notin
//    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.in, lhs, rhs)) =>
//      OperEx(TlaSetOper.notin, lhs, rhs)

    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.notin, lhs, rhs)) =>
      OperEx(TlaSetOper.in, lhs, rhs)

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(!left || right))

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(false)), _) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(true)), right) =>
      simplifyShallow(OperEx(TlaBoolOper.not, right))

    case OperEx(TlaBoolOper.implies, lhs, ValEx(TlaBool(true))) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.implies, lhs, ValEx(TlaBool(false))) =>
      simplifyShallow(OperEx(TlaBoolOper.not, lhs))

    case OperEx(TlaBoolOper.equiv, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(left == right))

    case OperEx(TlaBoolOper.equiv, ValEx(TlaBool(left)), right) =>
      if (left) {
        right
      } else {
        simplifyShallow(OperEx(TlaBoolOper.not, right))
      }

    case OperEx(TlaBoolOper.equiv, left, ValEx(TlaBool(right))) =>
      if (right) {
        left
      } else {
        simplifyShallow(OperEx(TlaBoolOper.not, left))
      }

      // many ite expressions can be simplified like this
    case OperEx(TlaControlOper.ifThenElse, ValEx(TlaBool(true)), thenEx, _) =>
      thenEx

    case OperEx(TlaControlOper.ifThenElse, ValEx(TlaBool(false)), _, elseEx) =>
      elseEx

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), elseEx) =>
      simplifyShallow(OperEx(TlaBoolOper.and, OperEx(TlaBoolOper.not, pred), elseEx))

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(true)), ValEx(TlaBool(false))) =>
      simplifyShallow(pred)

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), ValEx(TlaBool(true))) =>
      simplifyShallow(OperEx(TlaBoolOper.not, pred))

    case ite @ OperEx(TlaControlOper.ifThenElse, _, thenEx, elseEx) =>
      if (thenEx != elseEx) {
        ite
      } else {
        thenEx
      }

    // default
    case _ =>
      ex
  }
}

object ConstSimplifier {
  def apply(tracker: TransformationTracker): ConstSimplifier = new ConstSimplifier(tracker)
}
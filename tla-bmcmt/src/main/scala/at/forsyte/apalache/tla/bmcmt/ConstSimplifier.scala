package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * A simplifier of constant TLA+ expressions, e.g., rewriting 1 + 2 to 3.
  *
  * @author Igor Konnov
  */
class ConstSimplifier {
  def isFalseConst(ex: TlaEx): Boolean = {
    ex match {
      case ValEx(TlaBool(false)) => true
      case NameEx(name) => name == SolverContext.falseConst || name == Arena.falseName
      case _ => false
    }
  }

  def isTrueConst(ex: TlaEx): Boolean = {
    ex match {
      case ValEx(TlaBool(true)) => true
      case NameEx(name) => name == SolverContext.trueConst || name == Arena.trueName
      case _ => false
    }
  }

  def isBoolConst(ex: TlaEx): Boolean = isFalseConst(ex) || isTrueConst(ex)

  def simplify(rootExpr: TlaEx): TlaEx = {
    def rewriteDeep(ex: TlaEx): TlaEx = ex match {
      case NameEx(_) | ValEx(_) =>
        if (isFalseConst(ex)) {
          ValEx(TlaBool(false))
        } else if (isTrueConst(ex)) {
          ValEx(TlaBool(true))
        } else {
          ex
        }

      // do not go in tla.in and tla.notin, as it breaks down our SMT encoding
      // same for type annotations, if the simplifier introduces new expressions, type annotations may be broken
      case OperEx(TlaSetOper.in, _*) | OperEx(TlaSetOper.notin, _*) | OperEx(BmcOper.withType, _*) => ex

      case OperEx(oper, args @ _*) =>
        simplifyShallow(OperEx(oper, args map rewriteDeep :_*))

      case _ =>
        ex
    }

    rewriteDeep(rootExpr)
  }

  def simplifyShallow(ex: TlaEx): TlaEx = ex match {
    case NameEx(_) | ValEx(_) =>
      if (isFalseConst(ex)) {
        ValEx(TlaBool(false))
      } else if (isTrueConst(ex)) {
        ValEx(TlaBool(true))
      } else {
        ex
      }

    // do not go in tla.in and tla.notin, as it breaks down our SMT encoding
    case OperEx(TlaSetOper.in, _*) | OperEx(TlaSetOper.notin, _*) | OperEx(BmcOper.withType, _*) => ex

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
      OperEx(TlaBoolOper.and, args.filter(_ != ValEx(TlaBool(true))) :_*)

    case OperEx(TlaBoolOper.or, args @ _*) if args.contains(ValEx(TlaBool(true))) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.or, args @ _*) if args.forall (_.isInstanceOf[ValEx]) =>
      val result = args.contains(ValEx(TlaBool(true)))
      ValEx(TlaBool(result))

    case OperEx(TlaBoolOper.or, args @ _*)  =>
      OperEx(TlaBoolOper.or, args.filter(_ != ValEx(TlaBool(false))) :_*)

    case OperEx(TlaBoolOper.not, ValEx(TlaBool(b))) =>
      ValEx(TlaBool(!b))

    case OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, underDoubleNegation)) =>
      underDoubleNegation

    case OperEx(TlaBoolOper.not, OperEx(TlaOper.ne, lhs, rhs)) =>
      OperEx(TlaOper.eq, lhs, rhs)

    case OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, lhs, rhs)) =>
      OperEx(TlaOper.ne, lhs, rhs)

    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.in, lhs, rhs)) =>
      OperEx(TlaSetOper.notin, lhs, rhs)

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
    case OperEx(TlaControlOper.ifThenElse, pred, thenEx, _) if isTrueConst(pred) =>
      thenEx

    case OperEx(TlaControlOper.ifThenElse, pred, _, elseEx) if isFalseConst(pred) =>
      elseEx

    case ite @ OperEx(TlaControlOper.ifThenElse, _, thenEx, elseEx) =>
      if (thenEx != elseEx) {
        ite
      } else {
        thenEx
      }

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(true)), ValEx(TlaBool(false))) =>
      pred

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), ValEx(TlaBool(true))) =>
      OperEx(TlaBoolOper.not, pred)

    // default
    case _ =>
      ex
  }

}

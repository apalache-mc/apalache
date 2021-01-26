package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

import scala.math.BigInt

/**
  * <p>A base class for constant simplification that is shared by more specialized simplifiers.</p>
  *
  * <p>Bugfix #450: make sure that the integers are simplified with BigInt.</p>
  *
  * @author Igor Konnov
  */
abstract class ConstSimplifierBase {

  /**
    * A shallow simplification that does not recurse into the expression structure.
    */
  def simplifyShallow: TlaEx => TlaEx = {
    case OperEx(TlaSetOper.notin, lhs, rhs) =>
      OperEx(TlaBoolOper.not, OperEx(TlaSetOper.in, lhs, rhs))

    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.notin, lhs, rhs)) =>
      OperEx(TlaSetOper.in, lhs, rhs)

    // integer operations
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      if (left == 0) {
        ValEx(TlaInt(right))
      } else if (right == 0) {
        ValEx(TlaInt(left))
      } else {
        ValEx(TlaInt(left + right))
      }

    case OperEx(
        TlaArithOper.minus,
        ValEx(TlaInt(left)),
        ValEx(TlaInt(right))
        ) =>
      ValEx(TlaInt(left - right))

    case ex @ OperEx(TlaArithOper.minus, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaInt(0)) else ex // this actually happens

    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      if (left == 0 || right == 0) {
        ValEx(TlaInt(BigInt(0)))
      } else if (left == 1) {
        ValEx(TlaInt(right))
      } else if (right == 1) {
        ValEx(TlaInt(left))
      } else {
        ValEx(TlaInt(left * right))
      }

    case OperEx(TlaArithOper.div, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left / right))

    case OperEx(TlaArithOper.mod, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left % right))

    case OperEx(TlaArithOper.exp, ValEx(TlaInt(base)), ValEx(TlaInt(power))) =>
      if (power.isValidInt) {
        ValEx(TlaInt(base.pow(power.toInt)))
      } else {
        // the power does not fit into an integer. That is a lot. Use doubles.
        val pow = Math.pow(base.toDouble, power.toDouble)
        val powAsBigInt =
          BigDecimal(pow).setScale(0, BigDecimal.RoundingMode.DOWN).toBigInt()
        ValEx(TlaInt(powAsBigInt))
      }

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

    case ex @ OperEx(TlaOper.eq, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaBool(true)) else ex

    case ex @ OperEx(TlaOper.eq, ValEx(TlaStr(left)), ValEx(TlaStr(right))) =>
      // bugfix #197
      if (left == right) ValEx(TlaBool(true)) else ex

    case OperEx(TlaOper.ne, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left != right))

    case ex @ OperEx(TlaOper.ne, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaBool(false)) else ex

    case ex @ OperEx(TlaOper.eq, ValEx(TlaStr(left)), ValEx(TlaStr(right))) =>
      // bugfix #197
      if (left == right) ValEx(TlaBool(false)) else ex

    // boolean operations
    case OperEx(TlaBoolOper.and, args @ _*) =>
      val simpArgs = args.filterNot { _ == ValEx(TlaBool(true)) }
      if (simpArgs.isEmpty) {
        ValEx(TlaBool(true)) // an empty conjunction is true
      } else if (simpArgs.contains(ValEx(TlaBool(false)))) {
        ValEx(TlaBool(false)) // one false make conjunction false
      } else {
        OperEx(TlaBoolOper.and, simpArgs: _*)
      }

    case OperEx(TlaBoolOper.or, args @ _*) =>
      val simpArgs = args.filterNot { _ == ValEx(TlaBool(false)) }
      if (simpArgs.isEmpty) {
        ValEx(TlaBool(false)) // an empty disjunction is true
      } else if (simpArgs.contains(ValEx(TlaBool(true)))) {
        ValEx(TlaBool(true)) // one true make disjunction true
      } else {
        OperEx(TlaBoolOper.or, simpArgs: _*)
      }

    case OperEx(TlaBoolOper.not, ValEx(TlaBool(b))) =>
      ValEx(TlaBool(!b))

    case OperEx(
        TlaBoolOper.not,
        OperEx(TlaBoolOper.not, underDoubleNegation)
        ) =>
      underDoubleNegation

    case OperEx(TlaBoolOper.not, OperEx(TlaOper.ne, lhs, rhs)) =>
      OperEx(TlaOper.eq, lhs, rhs)

    case OperEx(
        TlaBoolOper.implies,
        ValEx(TlaBool(left)),
        ValEx(TlaBool(right))
        ) =>
      ValEx(TlaBool(!left || right))

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(false)), _) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(true)), right) =>
      simplifyShallow(OperEx(TlaBoolOper.not, right))

    case OperEx(TlaBoolOper.implies, _, ValEx(TlaBool(true))) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.implies, lhs, ValEx(TlaBool(false))) =>
      simplifyShallow(OperEx(TlaBoolOper.not, lhs))

    case OperEx(
        TlaBoolOper.equiv,
        ValEx(TlaBool(left)),
        ValEx(TlaBool(right))
        ) =>
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

    case OperEx(
        TlaControlOper.ifThenElse,
        pred,
        ValEx(TlaBool(false)),
        elseEx
        ) =>
      OperEx(TlaBoolOper.and, OperEx(TlaBoolOper.not, pred), elseEx)

    case OperEx(
        TlaControlOper.ifThenElse,
        pred,
        ValEx(TlaBool(true)),
        ValEx(TlaBool(false))
        ) =>
      pred

    case OperEx(
        TlaControlOper.ifThenElse,
        pred,
        ValEx(TlaBool(false)),
        ValEx(TlaBool(true))
        ) =>
      OperEx(TlaBoolOper.not, pred)

    case ite @ OperEx(TlaControlOper.ifThenElse, _, thenEx, elseEx) =>
      if (thenEx != elseEx) {
        ite
      } else {
        thenEx
      }

    // default
    case ex =>
      ex
  }

}

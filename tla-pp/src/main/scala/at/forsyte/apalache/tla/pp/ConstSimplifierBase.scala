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
  private val boolTag = Typed(BoolT1())
  private val intTag = Typed(IntT1())

  /**
   * A shallow simplification that does not recurse into the expression structure.
   */
  def simplifyShallow: TlaEx => TlaEx = {
    case OperEx(TlaSetOper.notin, lhs, rhs) =>
      OperEx(TlaBoolOper.not, OperEx(TlaSetOper.in, lhs, rhs)(boolTag))(boolTag)

    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.notin, lhs, rhs)) =>
      OperEx(TlaSetOper.in, lhs, rhs)(boolTag)

    // integer operations
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left + right))(intTag)

    // 0 + x = x
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), rightEx) =>
      if (left == 0) {
        rightEx
      } else {
        OperEx(TlaArithOper.plus, ValEx(TlaInt(left))(intTag), rightEx)(intTag)
      }

    // x + 0 = x
    case OperEx(TlaArithOper.plus, leftEx, ValEx(TlaInt(right))) =>
      if (right == 0) {
        leftEx
      } else {
        OperEx(TlaArithOper.plus, leftEx, ValEx(TlaInt(right))(intTag))(intTag)
      }

    case OperEx(TlaArithOper.minus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left - right))(intTag)

    // 0 - x = -x
    case OperEx(TlaArithOper.minus, ValEx(TlaInt(left)), rightEx) =>
      if (left == 0) {
        // TODO: 0 - 1 should be ValInt(-1)
        OperEx(TlaArithOper.uminus, rightEx)(intTag)
      } else {
        OperEx(TlaArithOper.minus, ValEx(TlaInt(left))(intTag), rightEx)(intTag)
      }

    // x - 0 = x
    case OperEx(TlaArithOper.minus, leftEx, ValEx(TlaInt(right))) =>
      if (right == 0) {
        leftEx
      } else {
        OperEx(TlaArithOper.minus, leftEx, ValEx(TlaInt(right))(intTag))(intTag)
      }

    // x - x = 0
    case ex @ OperEx(TlaArithOper.minus, leftEx, rightEx) =>
      if (leftEx == rightEx) ValEx(TlaInt(0))(intTag) else ex // this actually happens

    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left * right))(intTag)

    // 0 * x = 0
    // 1 * x = x
    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), rightEx) =>
      if (left == 0) {
        ValEx(TlaInt(0))(intTag)
      } else if (left == 1) {
        rightEx
      } else {
        OperEx(TlaArithOper.mult, ValEx(TlaInt(left))(intTag), rightEx)(intTag)
      }

    // x * 0 = 0
    // x * 1 = x
    case OperEx(TlaArithOper.mult, leftEx, ValEx(TlaInt(right))) =>
      if (right == 0) {
        ValEx(TlaInt(0))(intTag)
      } else if (right == 1) {
        leftEx
      } else {
        OperEx(TlaArithOper.mult, leftEx, ValEx(TlaInt(right))(intTag))(intTag)
      }

    case ex @ OperEx(TlaArithOper.div, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      if (right == 0) {
        throw new IllegalArgumentException(s"Division by zero at ${ex.toString}")
      } else {
        ValEx(TlaInt(left / right))(intTag)
      }

    // 0 / x = 0
    case OperEx(TlaArithOper.div, ValEx(TlaInt(left)), rightEx) =>
      if (left == 0) {
        ValEx(TlaInt(0))(intTag)
      } else {
        OperEx(TlaArithOper.div, ValEx(TlaInt(left))(intTag), rightEx)(intTag)
      }

    // x / 1 = x
    case ex @ OperEx(TlaArithOper.div, leftEx, ValEx(TlaInt(right))) =>
      if (right == 0) {
        throw new IllegalArgumentException(s"Division by zero at ${ex.toString}")
      } else if (right == 1) {
        leftEx
      } else {
        OperEx(TlaArithOper.div, leftEx, ValEx(TlaInt(right))(intTag))(intTag)
      }

    // x / x = 1
    case ex @ OperEx(TlaArithOper.div, leftEx, rightEx) =>
      if (leftEx == rightEx) {
        ValEx(TlaInt(1))(intTag)
      } else {
        OperEx(TlaArithOper.div, leftEx, rightEx)(intTag)
      }

    case ex @ OperEx(TlaArithOper.mod, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      if (right == 0) {
        throw new IllegalArgumentException(s"Mod by zero at ${ex.toString}")
      } else {
        ValEx(TlaInt(left % right))(intTag)
      }

    // x % 1 = 0
    case ex @ OperEx(TlaArithOper.mod, leftEx, ValEx(TlaInt(right))) =>
      if (right == 0) {
        throw new IllegalArgumentException(s"Mod by zero at ${ex.toString}")
      } else if (right == 1) {
        ValEx(TlaInt(0))(intTag)
      } else {
        OperEx(TlaArithOper.mod, leftEx, ValEx(TlaInt(right))(intTag))(intTag)
      }

    // x % x = 0
    case OperEx(TlaArithOper.mod, leftEx, rightEx) =>
      if (leftEx == rightEx) {
        ValEx(TlaInt(0))(intTag)
      } else {
        OperEx(TlaArithOper.mod, leftEx, rightEx)(intTag)
      }

    case ex @ OperEx(TlaArithOper.exp, ValEx(TlaInt(base)), ValEx(TlaInt(power))) =>
      if (power < 0) {
        throw new IllegalArgumentException(s"Negative power at ${ex.toString}")
      } else {
        try {
          ValEx(TlaInt(base.pow(power.toInt)))(intTag)
        } catch {
          case _ : ArithmeticException =>
            // the power does not fit into an integer. That is a lot. Use doubles.
            val pow = Math.pow(base.toDouble, power.toDouble)
            val powAsBigInt = BigDecimal(pow).setScale(0, BigDecimal.RoundingMode.DOWN).toBigInt()
            ValEx(TlaInt(powAsBigInt))(intTag)
        }
      }

    // x ^ 0 = 1
    // x ^ 1 = x
    case OperEx(TlaArithOper.exp, leftEx, ValEx(TlaInt(right))) =>
      if (right == 0) {
        ValEx(TlaInt(1))(intTag)
      } else if (right == 1) {
        leftEx
      } else {
        OperEx(TlaArithOper.exp, leftEx, ValEx(TlaInt(right))(intTag))(intTag)
      }

    // 0 ^ x = 0 (except if x = 0 which will match the previous case)
    // 1 ^ x = 1
    case OperEx(TlaArithOper.exp, ValEx(TlaInt(left)), rightEx) =>
      if (left == 0) {
        ValEx(TlaInt(0))(intTag)
      } else if (left == 1) {
        ValEx(TlaInt(1))(intTag)
      } else {
        OperEx(TlaArithOper.exp, ValEx(TlaInt(left))(intTag), rightEx)(intTag)
      }

    case OperEx(TlaArithOper.uminus, ValEx(TlaInt(value))) =>
      if (value == 0) ValEx(TlaInt(0))(intTag) else ValEx(TlaInt(-value))(intTag)

    case OperEx(TlaArithOper.lt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left < right))(boolTag)

    case OperEx(TlaArithOper.le, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left <= right))(boolTag)

    case OperEx(TlaArithOper.gt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left > right))(boolTag)

    case OperEx(TlaArithOper.ge, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left >= right))(boolTag)

    case OperEx(TlaOper.eq, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left == right))(boolTag)

    case ex @ OperEx(TlaOper.eq, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaBool(true))(boolTag) else ex

    case ex @ OperEx(TlaOper.eq, ValEx(TlaStr(left)), ValEx(TlaStr(right))) =>
      // bugfix #197
      if (left == right) ValEx(TlaBool(true))(boolTag) else ex

    case OperEx(TlaOper.ne, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left != right))(boolTag)

    case ex @ OperEx(TlaOper.ne, NameEx(left), NameEx(right)) =>
      if (left == right) ValEx(TlaBool(false))(boolTag) else ex

    case ex @ OperEx(TlaOper.ne, ValEx(TlaStr(left)), ValEx(TlaStr(right))) =>
      // bugfix #197
      if (left == right) ValEx(TlaBool(false))(boolTag) else ex

    // boolean operations
    case OperEx(TlaBoolOper.and, args @ _*) =>
      val simpArgs = args.filterNot {
        _ == ValEx(TlaBool(true))(boolTag)
      }
      if (simpArgs.isEmpty) {
        ValEx(TlaBool(true))(boolTag) // an empty conjunction is true
      } else if (simpArgs.contains(ValEx(TlaBool(false))(boolTag))) {
        ValEx(TlaBool(false))(boolTag) // one false make conjunction false
      } else {
        OperEx(TlaBoolOper.and, simpArgs: _*)(boolTag)
      }

    case OperEx(TlaBoolOper.or, args @ _*) =>
      val simpArgs = args.filterNot {
        _ == ValEx(TlaBool(false))(boolTag)
      }
      if (simpArgs.isEmpty) {
        ValEx(TlaBool(false))(boolTag) // an empty disjunction is true
      } else if (simpArgs.contains(ValEx(TlaBool(true))(boolTag))) {
        ValEx(TlaBool(true))(boolTag) // one true make disjunction true
      } else {
        OperEx(TlaBoolOper.or, simpArgs: _*)(boolTag)
      }

    case OperEx(TlaBoolOper.not, ValEx(TlaBool(b))) =>
      ValEx(TlaBool(!b))(boolTag)

    case OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, underDoubleNegation)) =>
      underDoubleNegation

    case OperEx(TlaBoolOper.not, OperEx(TlaOper.ne, lhs, rhs)) =>
      OperEx(TlaOper.eq, lhs, rhs)(boolTag)

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(!left || right))(boolTag)

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(false)), _) =>
      ValEx(TlaBool(true))(boolTag)

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(true)), right) =>
      simplifyShallow(OperEx(TlaBoolOper.not, right)(boolTag))

    case OperEx(TlaBoolOper.implies, _, ValEx(TlaBool(true))) =>
      ValEx(TlaBool(true))(boolTag)

    case OperEx(TlaBoolOper.implies, lhs, ValEx(TlaBool(false))) =>
      simplifyShallow(OperEx(TlaBoolOper.not, lhs)(boolTag))

    case OperEx(TlaBoolOper.equiv, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(left == right))(boolTag)

    case OperEx(TlaBoolOper.equiv, ValEx(TlaBool(left)), right) =>
      if (left) {
        right
      } else {
        simplifyShallow(OperEx(TlaBoolOper.not, right)(boolTag))
      }

    case OperEx(TlaBoolOper.equiv, left, ValEx(TlaBool(right))) =>
      if (right) {
        left
      } else {
        simplifyShallow(OperEx(TlaBoolOper.not, left)(boolTag))
      }

    // many ite expressions can be simplified like this
    case OperEx(TlaControlOper.ifThenElse, ValEx(TlaBool(true)), thenEx, _) =>
      thenEx

    case OperEx(TlaControlOper.ifThenElse, ValEx(TlaBool(false)), _, elseEx) =>
      elseEx

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), elseEx) =>
      OperEx(TlaBoolOper.and, OperEx(TlaBoolOper.not, pred)(boolTag), elseEx)(boolTag)

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(true)), ValEx(TlaBool(false))) =>
      pred

    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), ValEx(TlaBool(true))) =>
      OperEx(TlaBoolOper.not, pred)(boolTag)

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

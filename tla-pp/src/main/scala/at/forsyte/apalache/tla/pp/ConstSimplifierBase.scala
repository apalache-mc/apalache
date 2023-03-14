package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.types.tla

/**
 * <p>A base class for constant simplification that is shared by more specialized simplifiers.</p>
 *
 * <p>Bugfix #450: make sure that the integers are simplified with BigInt.</p>
 *
 * @author
 *   Igor Konnov
 */
abstract class ConstSimplifierBase {
  private val boolTag = Typed(BoolT1)
  private val intTag = Typed(IntT1)

  private def trueEx = ValEx(TlaBool(true))(boolTag)
  private def falseEx = ValEx(TlaBool(false))(boolTag)
  private def emptySet(tag: TypeTag) = OperEx(TlaSetOper.enumSet)(tag)

  /**
   * A shallow simplification that does not recurse into the expression structure.
   */
  def simplifyShallow: TlaEx => TlaEx = {
    // !FALSE = TRUE
    // !TRUE = FALSE
    case OperEx(TlaBoolOper.not, ValEx(TlaBool(b))) => ValEx(TlaBool(!b))(boolTag)

    // !!x = x
    case OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, underDoubleNegation)) => underDoubleNegation

    // Relace \neq with \eq
    // x /= y = !(x = y)
    case OperEx(TlaOper.ne, lhs, rhs) =>
      val equality = simplifyShallow(OperEx(TlaOper.eq, lhs, rhs)(boolTag))
      simplifyShallow(OperEx(TlaBoolOper.not, equality)(boolTag))
    // !(x /= y) = x = y
    case OperEx(TlaBoolOper.not, OperEx(TlaOper.ne, lhs, rhs)) => simplifyShallow(OperEx(TlaOper.eq, lhs, rhs)(boolTag))

    // Replace \notin with \in
    // x \notin y = !(x \in y)
    case OperEx(TlaSetOper.notin, lhs, rhs) =>
      OperEx(TlaBoolOper.not, OperEx(TlaSetOper.in, lhs, rhs)(boolTag))(boolTag)
    // !(x \notin y) = x \in y
    case OperEx(TlaBoolOper.not, OperEx(TlaSetOper.notin, lhs, rhs)) => OperEx(TlaSetOper.in, lhs, rhs)(boolTag)

    // integer operations
    // Evaluate constant addition
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaInt(left + right))(intTag)
    // 0 + x = x
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), rightEx) if left == 0 => rightEx
    // x + 0 = x
    case OperEx(TlaArithOper.plus, leftEx, ValEx(TlaInt(right))) if right == 0 => leftEx

    // Evaluate constant subtraction
    case OperEx(TlaArithOper.minus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaInt(left - right))(intTag)
    // 0 - x = -x
    case OperEx(TlaArithOper.minus, ValEx(TlaInt(left)), rightEx) if left == 0 =>
      OperEx(TlaArithOper.uminus, rightEx)(intTag)
    // x - 0 = x
    case OperEx(TlaArithOper.minus, leftEx, ValEx(TlaInt(right))) if right == 0 => leftEx
    // x - x = 0 (this actually happens)
    case OperEx(TlaArithOper.minus, leftEx, rightEx) if (leftEx == rightEx) => ValEx(TlaInt(0))(intTag)

    // Evaluate constant multiplication
    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaInt(left * right))(intTag)
    // 0 * x = 0
    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), _) if (left == 0) => ValEx(TlaInt(0))(intTag)
    // 1 * x = x
    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), rightEx) if (left == 1) => rightEx
    // x * 0 = 0
    case OperEx(TlaArithOper.mult, _, ValEx(TlaInt(right))) if (right == 0) => ValEx(TlaInt(0))(intTag)
    // x * 1 = x
    case OperEx(TlaArithOper.mult, leftEx, ValEx(TlaInt(right))) if (right == 1) => leftEx

    // x / 0 = undefined
    case ex @ OperEx(TlaArithOper.div, _, ValEx(TlaInt(right))) if (right == 0) =>
      throw new TlaInputError(s"Division by zero at ${ex.toString}")
    // Evaluate constant division
    case OperEx(TlaArithOper.div, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaInt(left / right))(intTag)
    // 0 / x = 0
    case OperEx(TlaArithOper.div, ValEx(TlaInt(left)), _) if (left == 0) => ValEx(TlaInt(0))(intTag)
    // x / 1 = x
    case OperEx(TlaArithOper.div, leftEx, ValEx(TlaInt(right))) if (right == 1) => leftEx
    // x / x = 1
    case OperEx(TlaArithOper.div, leftEx, rightEx) if (leftEx == rightEx) => ValEx(TlaInt(1))(intTag)

    // x % 0 = undefined
    case ex @ OperEx(TlaArithOper.mod, _, ValEx(TlaInt(right))) if (right == 0) =>
      throw new TlaInputError(s"Mod by zero at ${ex.toString}")
    // Evaluate constant mod
    case OperEx(TlaArithOper.mod, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaInt(left % right))(intTag)
    // x % 1 = 0
    case OperEx(TlaArithOper.mod, _, ValEx(TlaInt(right))) if (right == 1) => ValEx(TlaInt(0))(intTag)
    // x % x = 0
    case OperEx(TlaArithOper.mod, leftEx, rightEx) if (leftEx == rightEx) => ValEx(TlaInt(0))(intTag)

    // 0 ^ 0 = undefined
    case OperEx(TlaArithOper.exp, ValEx(TlaInt(base)), ValEx(TlaInt(power))) if (base == 0 && power == 0) =>
      throw new TlaInputError(s"0 ^ 0 is undefined")
    // Try to evaluante constant exponentiation
    case ex @ OperEx(TlaArithOper.exp, ValEx(TlaInt(base)), ValEx(TlaInt(power))) =>
      if (power < 0) {
        throw new TlaInputError(s"Negative power at ${ex}")
      }
      if (!power.isValidInt) {
        throw new TlaInputError(s"The power at ${ex.toString} exceedes the limit of ${Int.MaxValue}")
      } else {
        // Use doubles to calculate since they have a reasonable size limit
        val estimatedPow = Math.pow(base.toDouble, power.toDouble)
        if (estimatedPow < Double.MinValue || estimatedPow > Double.MaxValue) {
          throw new TlaInputError(s"The result of ${ex.toString} exceedes the limit of ${Double.MaxValue}")
        }
        val pow = base.pow(power.toInt)
        ValEx(TlaInt(pow))(intTag)
      }

    // x ^ 0 = 1
    case OperEx(TlaArithOper.exp, _, ValEx(TlaInt(right))) if (right == 0) => ValEx(TlaInt(1))(intTag)
    // x ^ 1 = x
    case OperEx(TlaArithOper.exp, leftEx, ValEx(TlaInt(right))) if (right == 1) => leftEx
    // 0 ^ x = 0
    case OperEx(TlaArithOper.exp, ValEx(TlaInt(left)), _) if (left == 0) => ValEx(TlaInt(0))(intTag)
    // 1 ^ x = 1
    case OperEx(TlaArithOper.exp, ValEx(TlaInt(left)), _) if (left == 1) => ValEx(TlaInt(1))(intTag)

    // -0 = 0
    case OperEx(TlaArithOper.uminus, ValEx(TlaInt(value))) if (value == 0) => ValEx(TlaInt(0))(intTag)
    // Evaluate unary minus
    case OperEx(TlaArithOper.uminus, ValEx(TlaInt(value))) => ValEx(TlaInt(-value))(intTag)

    // Evaluate relational expressions between integers
    case OperEx(TlaArithOper.lt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaBool(left < right))(boolTag)
    case OperEx(TlaArithOper.le, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaBool(left <= right))(boolTag)
    case OperEx(TlaArithOper.gt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaBool(left > right))(boolTag)
    case OperEx(TlaArithOper.ge, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaBool(left >= right))(boolTag)

    // x == x = TRUE
    case OperEx(TlaOper.eq, left, right) if (left == right) => trueEx

    // Evaluate constant comparisson
    case OperEx(TlaOper.eq, ValEx(TlaInt(left)), ValEx(TlaInt(right))) => ValEx(TlaBool(left == right))(boolTag)
    // bugfix #197
    case OperEx(TlaOper.eq, ValEx(TlaStr(left)), ValEx(TlaStr(right))) => ValEx(TlaBool(left == right))(boolTag)

    // boolean operations
    case OperEx(TlaBoolOper.and, args @ _*) =>
      val simpArgs = args.filterNot {
        _ == trueEx
      }
      simpArgs match {
        case Seq()      => trueEx // an empty conjunction is true
        case Seq(first) => first
        // one false make conjunction false
        case _ if simpArgs.contains(falseEx) => falseEx
        // TRUE /\ x /\ y = x /\ y
        case _ => OperEx(TlaBoolOper.and, simpArgs: _*)(boolTag)
      }

    case OperEx(TlaBoolOper.or, args @ _*) =>
      val simpArgs = args.filterNot {
        _ == falseEx
      }
      simpArgs match {
        case Seq()      => falseEx // an empty disjunction is false
        case Seq(first) => first
        // one true make disjunction true
        case _ if simpArgs.contains(trueEx) => trueEx
        // FALSE \/ x \/ y = x \/ y
        case _ => OperEx(TlaBoolOper.or, simpArgs: _*)(boolTag)
      }

    // Evaluate implication of constants
    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(!left || right))(boolTag)
    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(false)), _) => trueEx
    case OperEx(TlaBoolOper.implies, _, ValEx(TlaBool(true)))  => trueEx

    // TRUE -> x = x
    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(true)), right) => right
    // x -> FALSE = !x
    case OperEx(TlaBoolOper.implies, lhs, ValEx(TlaBool(false))) =>
      simplifyShallow(OperEx(TlaBoolOper.not, lhs)(boolTag))

    // many ite expressions can be simplified like this
    // IF true THEN x ELSE y = x
    case OperEx(TlaControlOper.ifThenElse, ValEx(TlaBool(true)), thenEx, _) => thenEx
    // IF false THEN x ELSE y = y
    case OperEx(TlaControlOper.ifThenElse, ValEx(TlaBool(false)), _, elseEx) => elseEx
    // IF x THEN TRUE ELSE FALSE = x
    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(true)), ValEx(TlaBool(false))) => pred
    // IF x THEN FALSE ELSE TRUE = !x
    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), ValEx(TlaBool(true))) =>
      simplifyShallow(OperEx(TlaBoolOper.not, pred)(boolTag))
    // IF x THEN FALSE ELSE y = !x /\ y
    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(false)), elseEx) =>
      val newPredicate = simplifyShallow(OperEx(TlaBoolOper.not, pred)(boolTag))
      simplifyShallow(OperEx(TlaBoolOper.and, newPredicate, elseEx)(boolTag))
    // IF x THEN TRUE ELSE y = x \/ y
    case OperEx(TlaControlOper.ifThenElse, pred, ValEx(TlaBool(true)), elseEx) =>
      simplifyShallow(OperEx(TlaBoolOper.or, pred, elseEx)(boolTag))
    // IF x THEN y ELSE y = y
    case OperEx(TlaControlOper.ifThenElse, _, thenEx, elseEx) if (thenEx == elseEx) => thenEx

    // \E x \in {}: P <=> FALSE
    case OperEx(TlaBoolOper.exists, _, OperEx(TlaSetOper.enumSet), _) => falseEx
    // \A x \in {}: P <=> TRUE
    case OperEx(TlaBoolOper.forall, _, OperEx(TlaSetOper.enumSet), _) => trueEx

    // \E x \in S: TRUE <=> S /= {}
    case OperEx(TlaBoolOper.exists, _, set, ValEx(TlaBool(true))) =>
      simplifyShallow(OperEx(TlaOper.ne, set, emptySet(set.typeTag))(boolTag))
    // \E x \in S: FALSE <=> FALSE
    case OperEx(TlaBoolOper.exists, _, _, ValEx(TlaBool(false))) => falseEx
    // \A x \in S: TRUE <=> TRUE
    case OperEx(TlaBoolOper.forall, _, _, ValEx(TlaBool(true))) => trueEx
    // \A x \in S: FALSE <=> S = {}
    case OperEx(TlaBoolOper.forall, _, set, ValEx(TlaBool(false))) =>
      simplifyShallow(OperEx(TlaOper.eq, set, emptySet(set.typeTag))(boolTag))

    // [{} -> {}] <=> [{} -> {Gen(1)}]
    case funSet @ OperEx(TlaSetOper.funSet, OperEx(TlaSetOper.enumSet), OperEx(TlaSetOper.enumSet)) =>
      val funSetT = TlaType1.fromTypeTag(funSet.typeTag)
      funSetT match {
        case SetT1(FunT1(domElemT, cdmElemT)) =>
          val mockCdm = tla.enumSet(tla.gen(1, cdmElemT))
          simplifyShallow(tla.funSet(tla.emptySet(domElemT), mockCdm))
        case t =>
          throw new TypingException(s"Function-set $funSet should have a set-of-functions type, found: $t", funSet.ID)
      }
    // if A /= {}, then [ A -> {} ] <=> {}
    case funSet @ OperEx(TlaSetOper.funSet, _, OperEx(TlaSetOper.enumSet)) =>
      emptySet(funSet.typeTag)

    // default
    case ex =>
      ex
  }
}

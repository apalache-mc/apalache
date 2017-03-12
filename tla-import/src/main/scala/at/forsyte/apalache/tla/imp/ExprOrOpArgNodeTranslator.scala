package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.values.{TlaDecimal, TlaInt, TlaStr}
import tla2sany.semantic._

/**
  * Translate a TLA+ expression.
  *
  * @author konnov
  */
class ExprOrOpArgNodeTranslator {
  def translate: ExprOrOpArgNode => TlaEx = {
      // as tlatools do not provide us with a visitor pattern, we have to enumerate classes here
      case num: NumeralNode =>
        translateNumeral(num)

      case str: StringNode =>
        translateString(str)

      case dec: DecimalNode =>
        translateDecimal(dec)

      case opApp: OpApplNode =>
        new OpApplTranslator().translate(opApp)

      case n: ExprNode => throw new SanyImporterException("Unexpected subclass of tla2sany.ExprNode: " + n.getClass)
  }

  private def translateNumeral(node: NumeralNode) =
    if (node.bigVal() != null) {
      ValEx(TlaInt(node.bigVal()))
    } else {
      ValEx(TlaInt(node.`val`()))
    }

  private def translateString(str: StringNode) =
    // internalize the string, so several occurences of the same string are kept as the same object
    ValEx(TlaStr(str.getRep.toString.intern()))

  private def translateDecimal(dec: DecimalNode) =
    if (dec.bigVal() != null) {
      ValEx(TlaDecimal(dec.bigVal()))
    } else {
      // the normal math exponent is the negated scale
      ValEx(TlaDecimal(BigDecimal(dec.mantissa(), -dec.exponent())))
    }
}

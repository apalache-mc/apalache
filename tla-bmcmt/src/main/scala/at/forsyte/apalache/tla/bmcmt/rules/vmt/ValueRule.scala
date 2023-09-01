package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.formulas.Booleans.{False, True}
import at.forsyte.apalache.tla.lir.formulas.EUF.UninterpretedLiteral
import at.forsyte.apalache.tla.lir.formulas.Integers.IntLiteral
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.types.ModelValueHandler

/**
 * ValueRule handles the conversion of literals and names
 *
 * Assumption: all names appearing in the IR are unique
 *
 * @author
 *   Jure Kukovec
 */
class ValueRule extends FormulaRule {

  def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case ValEx(_: TlaInt | _: TlaStr | _: TlaBool) => true
      case _: NameEx                                 => true
      case OperEx(TlaActionOper.prime, _: NameEx)    => true
      case _                                         => false
    }

  import ValueRule._

  def apply(ex: TlaEx): TermBuilderT = {
    val term = ex match {
      case ValEx(v) =>
        v match {
          case TlaInt(i) => IntLiteral(i)
          case TlaStr(s) =>
            val (tlaType, id) = ModelValueHandler.typeAndIndex(s).getOrElse((StrT1, s))
            UninterpretedLiteral(id, UninterpretedSort(tlaType.toString))
          case TlaBool(b) => if (b) True else False
          case _          => throwOn(ex)
        }
      case nameEx: NameEx                           => termFromNameEx(nameEx)
      case OperEx(TlaActionOper.prime, nEx: NameEx) =>
        // Rename x' to x^ for VMT
        termFromNameEx(renamePrimesForVMT(nEx))
      case _ => throwOn(ex)
    }
    storeUninterpretedLiteralOrVar(term).map { _ => term}
  }
}

// Some generic utility methods
object ValueRule {

  def throwOn[T](ex: TlaEx): T =
    throw new RewriterException(s"ValueRule not applicable to $ex", ex)

  // helper method for variable construction.
  def termFromNameEx(ex: NameEx): Variable =
    ex.typeTag match {
      case Typed(tt: TlaType1) =>
        val sort = TlaType1ToSortConverter.sortFromType(tt)
        mkVariable(ex.name, sort)
      case Untyped =>
        mkVariable(ex.name, UntypedSort)
      case Typed(other) =>
        throw new RewriterException(s"Term construction is not supported: $other is not in TlaType1", ex)
    }
}

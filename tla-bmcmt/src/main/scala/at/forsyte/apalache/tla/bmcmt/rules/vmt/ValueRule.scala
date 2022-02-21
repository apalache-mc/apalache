package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{BoolVar, False, True}
import at.forsyte.apalache.tla.lir.formulas.EUF.{FunctionVar, UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.{IntLiteral, IntVar}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{FunctionSort, UninterpretedSort}
import at.forsyte.apalache.tla.lir.formulas.{Sort, StandardSorts, Term, Variable}
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, NameEx, OperEx, StrT1, TlaEx, TlaType1, Typed, Untyped, ValEx,
}
import at.forsyte.apalache.tla.typecheck.ModelValueHandler
import jdk.jshell.spi.ExecutionControl.NotImplementedException

// Handles the conversion of literals and names
// Assumption: all names appearing in the IR are unique
class ValueRule extends FormulaRule {

  def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case ValEx(_: TlaInt | _: TlaStr | _: TlaBool) => true
      case _: NameEx                                 => true
      case OperEx(TlaActionOper.prime, _: NameEx)    => true
      case _                                         => false
    }

  import ValueRule._

  def apply(ex: TlaEx): Term = ex match {
    case ValEx(v) =>
      v match {
        case TlaInt(i) => IntLiteral(i)
        case TlaStr(s) =>
          val (tlaType, id) = ModelValueHandler.typeAndIndex(s).getOrElse((StrT1(), s))
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
}

object ValueRule {

  def throwOn[T](ex: TlaEx): T =
    throw new RewriterException(s"ValueRule not applicable to $ex", ex)

  def termFromNameEx(ex: NameEx): Variable =
    ex.typeTag match {
      case Typed(tt: TlaType1) =>
        val sort = TermAndSortCaster.sortFromType(tt)
        mkVariable(ex.name, sort)

      case Untyped() =>
        new Variable(ex.name) {
          override val sort: Sort = StandardSorts.UntypedSort()
        }
      case _ => throw new NotImplementedException("Typed only supported for TlaType1.")
    }
}

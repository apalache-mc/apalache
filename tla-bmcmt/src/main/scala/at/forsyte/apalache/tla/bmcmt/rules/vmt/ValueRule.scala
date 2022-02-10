package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{BoolVar, False, True}
import at.forsyte.apalache.tla.lir.formulas.EUF.{UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.{IntLiteral, IntVar}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.UninterpretedSort
import at.forsyte.apalache.tla.lir.formulas.{StandardSorts, Term}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, IntT1, NameEx, StrT1, TlaEx, Typed, Untyped, ValEx}
import at.forsyte.apalache.tla.typecheck.ModelValueHandler

// Handles the conversion of literals and names
// Assumption: all names appearing in the IR are unique
class ValueRule extends FormulaRule {

  def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case ValEx(_: TlaInt | _: TlaStr | _: TlaBool) => true
      case _: NameEx                                 => true
      case _                                         => false
    }

  private def throwOn[T](ex: TlaEx): T =
    throw new RewriterException(s"ValueRule not applicable to $ex", ex)

  private def termFromNameEx(ex: NameEx): Term =
    ex.typeTag match {
      case Typed(tt) =>
        tt match {
          case IntT1()        => IntVar(ex.name)
          case BoolT1()       => BoolVar(ex.name)
          case StrT1()        => UninterpretedVar(ex.name, UninterpretedSort(tt.toString))
          case ConstT1(tName) => UninterpretedVar(ex.name, UninterpretedSort(tName))
          case _              => throwOn(ex)
        }
      case Untyped() => UninterpretedVar(ex.name, StandardSorts.UntypedSort())
    }

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
    case nameEx: NameEx => termFromNameEx(nameEx)
    case _              => throwOn(ex)

  }
}

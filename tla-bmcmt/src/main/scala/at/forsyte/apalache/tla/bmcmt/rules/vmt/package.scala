package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.formulas.Booleans.BoolVar
import at.forsyte.apalache.tla.lir.formulas.EUF.{FunctionVar, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.IntVar
import at.forsyte.apalache.tla.lir.formulas.{Sort, Variable}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts._

package object vmt {
  type ConstSetMapT = Map[String, UninterpretedSort]

  def VMTprimeName(s: String) = s"$s^"
  def renamePrimesForVMT(unprimedNameEx: NameEx): NameEx =
    NameEx(VMTprimeName(unprimedNameEx.name))(unprimedNameEx.typeTag)
  def nextName(name: String): String = s".$name"

  def mkVariable(name: String, sort: Sort): Variable = sort match {
    case IntSort()             => IntVar(name)
    case BoolSort()            => BoolVar(name)
    case fs: FunctionSort      => FunctionVar(name, fs)
    case us: UninterpretedSort => UninterpretedVar(name, us)
    case s                     => new Variable(name) { override val sort: Sort = s }
  }
}

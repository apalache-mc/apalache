package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.formulas.Booleans.BoolVar
import at.forsyte.apalache.tla.lir.formulas.EUF.{FunctionVar, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.IntVar
import at.forsyte.apalache.tla.lir.formulas.{Sort, Variable}
import at.forsyte.apalache.tla.lir.formulas._

package object vmt {
  type ConstSetMapT = Map[String, UninterpretedSort]

  /**
   * Since ' is not a legal symbol in SMTLIB, we have to choose a convention for the names of primed variables. If `x`
   * is a variable name, then `x^` is the name used to represent `x'` in SMTLIB.
   */
  def VMTprimeName(s: String) = s"$s^"
  // Apply VMTprimeName to NameEx directly
  def renamePrimesForVMT(unprimedNameEx: NameEx): NameEx =
    NameEx(VMTprimeName(unprimedNameEx.name))(unprimedNameEx.typeTag)

  /**
   * VMT uses a named function definition to explicitly annotate which pairs of symbols represent the current- and
   * next-state value of a system variable. If `x` represents the current-state value, and `x^` the next-state value,
   * then `.x` is the name of the binding function.
   */
  def nextName(name: String): String = s".$name"

  /**
   * Creates a `Variable` term, of the appropriate subtype, based on the sort.
   */
  def mkVariable(name: String, sort: Sort): Variable = sort match {
    case IntSort()             => IntVar(name)
    case BoolSort()            => BoolVar(name)
    case fs: FunctionSort      => FunctionVar(name, fs)
    case us: UninterpretedSort => UninterpretedVar(name, us)
    case s                     => new Variable(name) { override val sort: Sort = s }
  }
}

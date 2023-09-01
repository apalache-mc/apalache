package at.forsyte.apalache.tla.lir.formulas

import scala.annotation.unused

/**
 * A representation of an SMT/VMT sort. We only support non-parametric sorts at the moment.
 *
 * @author
 *   Jure Kukovec
 */
abstract class Sort(val sortName: String)

/**
 * A representation of an SMT term. Each term has a singular sort.
 *
 * @author
 *   Jure Kukovec
 */
trait Term {
  val sort: Sort
}

abstract class Variable(@unused name: String) extends Term

case object BoolSort extends Sort("Boolean")
case object IntSort extends Sort("Integer")
case object UntypedSort extends Sort("Untyped")
sealed case class UninterpretedSort(override val sortName: String) extends Sort(sortName)
sealed case class FunctionSort(to: Sort, from: Sort*) extends Sort("Function") {
  def arity: Int = from.size
}

/**
 * A representation of an SMT declaration.
 *
 * @author
 *   Jure Kukovec
 */
abstract class Declaration

sealed case class DeclareConst(name: String, sort: Sort) extends Declaration

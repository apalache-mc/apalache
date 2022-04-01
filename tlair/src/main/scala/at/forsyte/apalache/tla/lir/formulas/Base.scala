package at.forsyte.apalache.tla.lir.formulas

import scalaz.unused

/**
 * A representation of an SMT/VMT sort. We only support non-parametric sorts at the moment.
 *
 * @author
 *   Jure Kukovec
 */
abstract class Sort(val sortName: String)

/**
 * A representation of an SMT/VMT term. Each term has a singular sort.
 *
 * @author
 *   Jure Kukovec
 */
trait Term {
  val sort: Sort
}

abstract class Variable(val name: String) extends Term

sealed case class BoolSort() extends Sort("Boolean")
sealed case class IntSort() extends Sort("Integer")
sealed case class UntypedSort() extends Sort("Untyped")
sealed case class UninterpretedSort(override val sortName: String) extends Sort(sortName)
sealed case class FunctionSort(to: Sort, from: Sort*) extends Sort("Function") {
  def arity: Int = from.size
}

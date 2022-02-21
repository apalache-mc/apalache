package at.forsyte.apalache.tla.lir.formulas

import at.forsyte.apalache.tla.lir.formulas.StandardSorts.FunctionSort

abstract class Sort(val sortName: String)
trait HasSort {
  val sort: Sort
}

trait Term extends HasSort

abstract class Variable(name: String) extends Term

object StandardSorts {
  sealed case class BoolSort() extends Sort("Boolean")
  sealed case class IntSort() extends Sort("Integer")
  sealed case class UntypedSort() extends Sort("Untyped")
  sealed case class UninterpretedSort(override val sortName: String) extends Sort(sortName)
  sealed case class FunctionSort(to: Sort, from: Sort*) extends Sort("Function") {
    def arity: Int = from.size
  }
}

trait FnTerm extends Term {
  override val sort: FunctionSort
}

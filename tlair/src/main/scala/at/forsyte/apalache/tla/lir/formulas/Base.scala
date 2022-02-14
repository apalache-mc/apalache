package at.forsyte.apalache.tla.lir.formulas

abstract class Sort(val sortName: String)
trait HasSort {
  val sort: Sort
}

trait Term extends HasSort

abstract class Variable(name: String) extends Term

sealed case class Function(name: String, to: Sort, from: Sort*) {
  def arity: Int = from.size
}

object StandardSorts {
  sealed case class BoolSort() extends Sort("Boolean")
  sealed case class IntSort() extends Sort("Integer")
  sealed case class UntypedSort() extends Sort("Untyped")
  sealed case class UninterpretedSort(name: String) extends Sort(name)
}

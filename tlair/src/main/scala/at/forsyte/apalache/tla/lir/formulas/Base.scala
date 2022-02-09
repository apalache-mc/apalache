package at.forsyte.apalache.tla.lir.formulas

abstract class Sort(sortName: String)
abstract class AbstractTerm
trait Term[S <: Sort] extends AbstractTerm
abstract class Variable[S <: Sort](name: String) extends Term[S]

sealed case class Function[S <: Sort](to: S, from: Sort*) {
  def arity: Int = from.size
}

object StandardSorts {
  sealed case class BoolSort() extends Sort("Boolean")
  sealed case class IntSort() extends Sort("Boolean")
}

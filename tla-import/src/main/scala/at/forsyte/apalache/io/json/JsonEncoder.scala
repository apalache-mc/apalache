package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}

/**
 * A JsonEncoder defines a conversion from a TLA+ expression to a json (as represented by T)
 * @tparam T Any class extending JsonRepresentation
 */
trait JsonEncoder[T <: JsonRepresentation] {
  def apply(ex: TlaEx): T
  def apply(decl: TlaDecl): T
  def apply(module: TlaModule): T
  def makeRoot(modules: Traversable[TlaModule]): T
}

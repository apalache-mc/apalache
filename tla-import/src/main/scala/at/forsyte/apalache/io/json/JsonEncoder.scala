package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}

trait JsonEncoder[T <: JsonRepresentation] {
  def apply(ex: TlaEx): T
  def apply(decl: TlaDecl): T
  def apply(module: TlaModule): T
}

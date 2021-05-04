package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}

/**
 * A JsonDecoder defines a conversion from a json (as represented by T) to a TLA+ expression/declaration/module
 *
 * @tparam T Any class extending JsonRepresentation
 */
trait JsonDecoder[T <: JsonRepresentation] {
  def asTlaModule(moduleJson: T): TlaModule
  def asTlaDecl(declJson: T): TlaDecl
  def asTlaEx(exJson: T): TlaEx
  def fromRoot(rootJson: T): Traversable[TlaModule]
}

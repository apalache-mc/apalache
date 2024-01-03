package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}
import scala.util.Try

/**
 * A JsonDecoder defines a conversion from a json (as represented by T) to a TLA+ expression/declaration/module
 *
 * @tparam T
 *   Any class extending JsonRepresentation
 */
trait JsonDecoder[T <: JsonRepresentation] {
  def asTlaModule(moduleJson: T): TlaModule
  def asTlaDecl(declJson: T): TlaDecl
  def asTlaEx(exJson: T): TlaEx
  def fromRoot(rootJson: T): Seq[TlaModule]

  /**
   * Parse a json representation which holds only a single TLA module. This is our typical, and currently only supported
   * use case.
   *
   * @param json
   *   A JSON encoding of a TLA Module
   * @return
   *   `Success(m)` if the `json` can be parsed, correctly and it described a single module. Otherwise `Failure(t)`
   *   where `t` is a `Throwable` describing the error.
   */
  def fromSingleModule(json: T): Try[TlaModule]
}

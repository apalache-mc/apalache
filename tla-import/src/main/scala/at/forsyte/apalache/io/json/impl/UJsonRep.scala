package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonRepresentation

/**
 * A JsonRepresentation, using the ujson library. Wraps a ujson.Value
 */
sealed case class UJsonRep(protected[json] val value: ujson.Value) extends JsonRepresentation {
  override def toString: String = ujson.write(value, indent = 2, escapeUnicode = false)
}

package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonRepresentation

/**
 * A JsonRepresentation, using the ujson library. Wraps a ujson.Value
 */
sealed case class UJsonRep(protected[json] val value: ujson.Value) extends JsonRepresentation {
  override def toString: String = ujson.write(value, indent = 2, escapeUnicode = false)

  /**
   * If `this` represents a JSON object defining a field
   * `fieldName : val`, the method returns a Some(_), containing the representation of `val`,
   *  otherwise (if `this` is not an object or if it does not define a `fieldName` field) returns None.
   */
  override def getFieldOpt(fieldName: String): Option[this.type] = for {
    objAsMap <- value.objOpt
    fieldVal <- objAsMap.get(fieldName)
  } yield UJsonRep(fieldVal).asInstanceOf[UJsonRep.this.type]
}

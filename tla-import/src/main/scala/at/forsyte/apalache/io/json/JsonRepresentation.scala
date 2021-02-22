package at.forsyte.apalache.io.json

trait JsonRepresentation {
  def toString: String
}

sealed case class UJsonRep(protected[json] val value: ujson.Value) extends JsonRepresentation {
  override def toString: String = ujson.write(value, indent = 2, escapeUnicode = false)
}

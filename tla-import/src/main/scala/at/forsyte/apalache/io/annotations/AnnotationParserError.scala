package at.forsyte.apalache.io.annotations

class AnnotationParserError(message: String) extends Exception(message) {
  override def toString: String = {
    "Error parsing annotation: " + message
  }
}

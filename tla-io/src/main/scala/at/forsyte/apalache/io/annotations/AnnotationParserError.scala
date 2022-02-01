package at.forsyte.apalache.io.annotations

class AnnotationParserError(message: String) extends Exception(message) {
  override def toString: String = {
    "Annotation error: " + message
  }
}

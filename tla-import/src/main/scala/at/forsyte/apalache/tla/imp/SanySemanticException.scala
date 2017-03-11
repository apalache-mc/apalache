package at.forsyte.apalache.tla.imp

/**
  * This exception is thrown when SANY reports a semantic error.
  *
  * @author konnov
  */
class SanySemanticException(message: String) extends SanyException(message)

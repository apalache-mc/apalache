package at.forsyte.apalache.tla.imp

/**
  * This exception is thrown when SANY reports a syntax error.
  *
  * @author konnov
  */
class SanySyntaxException(message: String) extends SanyException(message)

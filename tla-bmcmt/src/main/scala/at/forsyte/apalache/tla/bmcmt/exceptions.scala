package at.forsyte.apalache.tla.bmcmt

/**
  * A generic error that occured in the model checker.
  *
  * @param message error message
  */
class CheckerException(message: String) extends Exception(message)

/**
  * This exception is thrown when no rewriting rule applies to the current state.
  *
  * @param message error message
  */
class RewriterException(message: String) extends CheckerException(message)
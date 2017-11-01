package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

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

/**
  * This exception is thrown when the structure of a TLA+ expression is unexpected.
  * @param message error message
  * @param ex the problematic expression
  */
class InvalidTlaExException(message: String, ex: TlaEx) extends  CheckerException(message)
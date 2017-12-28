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
  * This exception is thrown when QStateRewrite cannot find an applicable rule.
  * @param message error message
  */
class NoRuleException(message: String) extends RewriterException(message)

/**
  * This exception is thrown in case of problems with SMT encoding.
  *
  * @param message error message
  */
class SmtEncodingException(message: String) extends CheckerException(message)

/**
  * This exception is thrown when the structure of a TLA+ expression is unexpected.
  * @param message error message
  * @param ex the problematic expression
  */
class InvalidTlaExException(message: String, ex: TlaEx) extends  CheckerException(message)

/**
  * An internal error that was triggered by the consistency checking code.
  * The user should contact the developers.
  *
  * @param message error message
  */
class InternalCheckerError(message: String) extends CheckerException(message)

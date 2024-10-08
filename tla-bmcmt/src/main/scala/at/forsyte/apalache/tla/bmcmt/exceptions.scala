package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * A generic error that occurred in the model checker.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class CheckerException(message: String, val causeExpr: TlaEx) extends Exception(message)

/**
 * This exception is thrown when no rewriting rule applies to the current state.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class RewriterException(message: String, causeExpr: TlaEx) extends CheckerException(message, causeExpr)

/**
 * This exception is thrown when the rewriter meets a generally well-formed TLA+ expression that cannot be handled due
 * to some known limitations of the model checker.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class RewriterKnownLimitationError(message: String, causeExpr: TlaEx) extends CheckerException(message, causeExpr)

/**
 * This exception is thrown when QStateRewrite cannot find an applicable rule.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class NoRuleException(message: String, causeExpr: TlaEx) extends RewriterException(message, causeExpr)

/**
 * This exception is thrown in case of problems with SMT encoding.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class SmtEncodingException(message: String, causeExpr: TlaEx) extends CheckerException(message, causeExpr)

/**
 * This exception is thrown when the structure of a TLA+ expression is unexpected.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class InvalidTlaExException(message: String, causeExpr: TlaEx) extends CheckerException(message, causeExpr)

/**
 * An internal error that was triggered by the consistency checking code. The user should contact the developers.
 *
 * @param message
 *   error message
 * @param causeExpr
 *   the problematic TLA+ expression, may be NullEx
 */
class InternalCheckerError(message: String, causeExpr: TlaEx) extends CheckerException(message, causeExpr)

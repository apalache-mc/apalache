package at.forsyte.apalache.tla.lir

// All exceptions related to the intermediate language should go here

/**
 * A general exception related to the intermediate language.
 *
 * @param message the error message
 */
class LirError(message: String) extends Exception(message)

/**
 * An exception that should be thrown when a TLA+ expression (or a module) does not fit into the expected fragment.
 *
 * @param message   the error message
 * @param failedIds the identified of the expressions that caused trouble
 */
class LanguagePredError(message: String, val failedIds: Seq[(UID, String)]) extends LirError(message)

/**
 * An exception that should be thrown when a TLA+ expression is malformed.
 *
 * @param message the error message
 */
class MalformedTlaError(message: String, val causeExpr: TlaEx) extends LirError(message)

/**
 * This exception is thrown when an input specification is malformed at the declaration or module level.
 * For malformed expressions, use MalformedTlaException
 *
 * @param message   the error message
 */
class MalformedSepecificationError(message: String) extends Exception(message)

/**
 * An exception that originated in an expression builder
 *
 * @param message the error message
 */
class BuilderError(message: String) extends LirError(message)

/**
 * An exception that should be thrown when a user-defined operator calls itself via a chain of calls to other
 * operators (in a non-recursive case).
 *
 * @param message the error message
 */
class CyclicDependencyError(message: String) extends LirError(message)

/**
 * This exception is thrown, whenever the code finds an irrecoverable error in expression types.
 *
 * @author konnov
 */
class TypingException(message: String) extends Exception(message)

/**
 * This exception is thrown when an outdated type annotation (pre 0.12.0) is met.
 *
 * @param message   the error message
 * @param causeExpr the expression that caused the error
 */
class OutdatedAnnotationsError(message: String, val causeExpr: TlaEx) extends LirError(message)

/**
 * This exception is thrown when an unsupported TLA+ feature is encountered
 *
 * @param message   the error message
 */
class UnsupportedFeatureError(message: String) extends Exception(message)

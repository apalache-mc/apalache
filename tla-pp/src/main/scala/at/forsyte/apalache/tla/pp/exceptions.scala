package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{MalformedTlaError, TlaEx, UID}

// All exceptions related to the intermediate language should go here

/**
 * An exception that should be thrown when a TLA+ expression (or a module) does not fit into the expected fragment.
 * @param message the error message
 */
class NotInKeraError(message: String, cause: TlaEx) extends MalformedTlaError(message, cause)

/**
 * This exception is thrown when operator overriding fails.
 * @param message the error message
 * @param cause the problematic expression
 */
class OverridingError(message: String, cause: TlaEx) extends MalformedTlaError(message, cause)

/**
 * An exception that should be thrown when preprocessing steps resulted in an irrecoverable error.
 * This exception should be treated as a bug, so a stack trace is expected.
 *
 * @param message the error message
 */
class IrrecoverablePreprocessingError(message: String) extends Exception(message)

/**
 * An exception that should be thrown when something is wrong with the tool configuration, input parameters, etc.
 * This exception should be treated as the input error: no stack trace, normal messages.
 *
 * @param message the error message
 */
class ConfigurationError(message: String) extends Exception(message)

/**
 * An exception that should be thrown when the TLA+ code is not following the Apalache guidelines, e.g.,
 * missing annotations for the recursive operators.
 * This exception should be treated as the input error: no stack trace, normal messages.
 *
 * @param message  error message
 * @param sourceId optional id of the expression (or declaration) that caused the error
 */
class TlaInputError(message: String, val sourceId: Option[UID] = None) extends Exception(message)

/**
 * An exception that should be thrown when a TLC configuration is wrong/not-found
 * @param message the error message
 */
class TLCConfigurationError(message: String) extends ConfigurationError(message)

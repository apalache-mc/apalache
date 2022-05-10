package at.forsyte.apalache.io

/**
 * An exception that should be thrown when something is wrong with the tool configuration, input parameters, etc. This
 * exception should be treated as the input error: no stack trace, normal messages.
 *
 * @param message
 *   the error message
 */
class ConfigurationError(message: String) extends Exception(message)

/**
 * An exception that should be thrown when something pretty printing fails
 *
 * This is considered a bug and should result in a stack trace.
 *
 * @param message
 *   the error message
 */
class PrettyPrinterError(message: String) extends Exception(message)

package at.forsyte.apalache.infra

/**
 * An error that occurs when executing a sequence of passes
 *
 * @param message
 *   an error message
 */
class PassExecException(message: String) extends Exception(message)

/**
 * An error that happened while processing options
 * @param message
 *   an error message
 */
class PassOptionException(message: String) extends Exception(message)

/**
 * An error that has been adapted by an [[ExceptionAdapter]]
 * @param err
 *   the [[ErrorMessage]] into which the originating error was adapted
 */
class AdaptedException(val err: ErrorMessage) extends Exception(err.msg)

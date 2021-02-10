/*
 We group all exceptions in a single file.

 See the Scala style guide: http://docs.scala-lang.org/style/files.html
 */

package at.forsyte.apalache.tla.typecheck

/**
 * This exception is thrown, whenever the type checker finds an irrecoverable error.
 *
 * @author konnov
 */
class TypingException(message: String) extends Exception(message)

/**
 * This exception is thrown, whenever the type checker finds an irrecoverable error in the user input.
 *
 * @author konnov
 */
class TypingInputException(message: String) extends TypingException(message)

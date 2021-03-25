/*
 We group all exceptions in a single file.

 See the Scala style guide: http://docs.scala-lang.org/style/files.html
 */

package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.TypingException

/**
 * This exception is thrown, whenever the type checker finds an irrecoverable error in the user input.
 *
 * @author konnov
 */
class TypingInputException(message: String) extends TypingException(message)

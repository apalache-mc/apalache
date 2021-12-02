/*
 We group all exceptions in a single file.

 See the Scala style guide: http://docs.scala-lang.org/style/files.html
 */

package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{TypingException, UID}

/**
 * This exception is thrown, whenever the type checker finds an irrecoverable error in the user input.
 *
 * @param message error message
 * @param causeExprId the id of a problematic expression, may be UID.nullId
 */
class TypingInputException(message: String, causeExprId: UID) extends TypingException(message, causeExprId)

/*
 We group all exceptions in a single file.

 See the Scala style guide: http://docs.scala-lang.org/style/files.html
 */

package at.forsyte.apalache.tla.imp

/**
  * This exception is thrown, whenever a call to SANY resulted in an error.
  * For more detailed causes, see the exceptions that inherit from SanyException.
  *
  * @author konnov
  */
class SanyException(message: String) extends Exception(message)

/**
  * This exception is thrown when our SanyImporter meets something unexpected.
  *
  * @author konnov
  */
class SanyImporterException(message: String) extends SanyException(message)

/**
  * This exception is thrown when SANY aborts.
  *
  * @author konnov
  */
class SanyAbortException(message: String) extends SanyException(message)

/**
  * This exception is thrown when SANY reports a syntax error.
  *
  * @author konnov
  */
class SanySyntaxException(message: String) extends SanyException(message)

/**
  * This exception is thrown when SANY reports a semantic error.
  *
  * @author konnov
  */
class SanySemanticException(message: String) extends SanyException(message)

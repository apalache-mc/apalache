package at.forsyte.apalache.tla.lir

// All exceptions related to the intermediate language should go here

/**
  * A general exception related to the intermediate language.
  * @param message the error message
  */
class LirError(message: String) extends Exception(message)

/**
  * An exception that should be thrown when a TLA+ expression (or a module) does not fit into the expected fragment.
  * @param message the error message
  */
class UnexpectedLanguageError(message: String) extends LirError(message)

/**
  * An exception that should be thrown when a TLA+ code is malformed.
  * @param message the error message
  */
class MalformedTlaError(message: String, val causeExpr: TlaEx) extends LirError(message)
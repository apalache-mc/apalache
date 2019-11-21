package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{MalformedTlaError, TlaEx}

// All exceptions related to the intermediate language should go here


/**
  * An exception that should be thrown when a TLA+ expression (or a module) does not fit into the expected fragment.
  * @param message the error message
  */
class NotInKeraError(message: String, cause: TlaEx) extends MalformedTlaError(message, cause)


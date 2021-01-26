package at.forsyte.apalache.tla.assignments

/**
  * An exception thrown to indicate a problem with assignments
  *
  * @param message a diagnostic message
  */
class AssignmentException(message: String) extends Exception(message)

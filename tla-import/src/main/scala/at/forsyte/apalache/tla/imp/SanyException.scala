package at.forsyte.apalache.tla.imp

/**
  * This exception is thrown, whenever a call to SANY resulted in an error.
  * For more detailed causes, see the exceptions that inherit from SanyException.
  *
  * @author konnov
  */
class SanyException(val message: String) extends Exception

package at.forsyte.apalache.tla.imp

/**
  * This exception is thrown when SANY aborts.
  *
  * @author konnov
  */
class SanyAbortException(message: String) extends SanyException(message)

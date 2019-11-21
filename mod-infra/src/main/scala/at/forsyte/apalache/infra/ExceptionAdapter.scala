package at.forsyte.apalache.infra

/**
  * ExceptionAdapter allows us to convert an exception into a message string.
  * The purpose of the adapter is to push the conversion in the DI container, where all required data is available,
  * e.g., source data.
  *
  * @author Igor Konnov
  */
trait ExceptionAdapter {
  def toMessage: PartialFunction[Exception, String]
}

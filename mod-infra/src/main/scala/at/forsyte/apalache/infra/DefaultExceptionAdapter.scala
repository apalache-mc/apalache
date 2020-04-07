package at.forsyte.apalache.infra

import javax.inject.Singleton

/**
  * The default adapter does nothing.
  */
@Singleton
class DefaultExceptionAdapter extends ExceptionAdapter {
  /**
    * Given an exception, the adapter produces an error message along with its severity.
    * @return
    */
  override def toMessage: PartialFunction[Exception, ErrorMessage] = PartialFunction.empty
}

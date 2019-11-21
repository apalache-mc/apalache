package at.forsyte.apalache.infra

import javax.inject.Singleton

/**
  * The default adapter does nothing.
  */
@Singleton
class DefaultExceptionAdapter extends ExceptionAdapter {
  override def toMessage: PartialFunction[Exception, String] = PartialFunction.empty
}

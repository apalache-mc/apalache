package at.forsyte.apalache.infra

import com.google.inject.Singleton

/**
 * The default adapter does nothing.
 */
@Singleton
class DefaultExceptionAdapter extends ExceptionAdapter {}

package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.infra.ExceptionAdapter
import com.typesafe.scalalogging.LazyLogging

import javax.inject.{Inject, Singleton}

// TODO: This can be removed in theory, but our current architecture requires executable passes
// include a injectable instance of `ExceptionAdapater`
/**
 * The adapter for all exceptions that can be produced when running the SANY parser and TlaImporter.
 *
 * @author
 *   Igor Konnv
 */
@Singleton
class ParserExceptionAdapter @Inject() () extends ExceptionAdapter with LazyLogging {}

package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TerminalPassWithTlaModule, WriteablePassOptions}
import at.forsyte.apalache.io.annotations.AnnotationStoreProvider
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.ParserExceptionAdapter
import com.google.inject.name.Names
import com.google.inject.{AbstractModule, TypeLiteral}

/**
 * A module that consists only of the parsing pass.
 *
 * @author Igor Konnov
 */
class ParserModule extends AbstractModule {
  override def configure(): Unit = {
    // the options singleton
    bind(classOf[PassOptions])
      .to(classOf[WriteablePassOptions])
    // exception handler
    bind(classOf[ExceptionAdapter])
      .to(classOf[ParserExceptionAdapter])
    // Create an annotation store with the custom provider.
    // We have to use TypeLiteral, as otherwise Guice is getting confused by type erasure.
    bind(new TypeLiteral[AnnotationStore]() {})
      .toProvider(classOf[AnnotationStoreProvider])

    // SanyParserPassImpl is the default implementation of SanyParserPass
    bind(classOf[SanyParserPass])
      .to(classOf[SanyParserPassImpl])
    // and it also the initial pass for PassChainExecutor
    bind(classOf[Pass])
      .annotatedWith(Names.named("InitialPass"))
      .to(classOf[SanyParserPass])
    // the next pass after SanyParserPass is the terminal pass
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterParser"))
      .to(classOf[TerminalPassWithTlaModule])
  }
}

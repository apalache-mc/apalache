package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.{DefaultExceptionAdapter, ExceptionAdapter}
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TerminalPassWithTlaModule, WriteablePassOptions}
import com.google.inject.AbstractModule
import com.google.inject.name.Names

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
      .to(classOf[DefaultExceptionAdapter])

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

package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TerminalPassWithTlaModule, WriteablePassOptions}
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import com.google.inject.AbstractModule
import com.google.inject.name.Names

class TypeCheckerModule extends AbstractModule {

  override def configure(): Unit = {
    // the options singleton
    bind(classOf[PassOptions])
      .to(classOf[WriteablePassOptions])
    // exception handler
    bind(classOf[ExceptionAdapter])
      .to(classOf[EtcTypeCheckerAdapter])

    // SanyParserPassImpl is the default implementation of SanyParserPass
    bind(classOf[SanyParserPass])
      .to(classOf[SanyParserPassImpl])
    // and it also the initial pass for PassChainExecutor
    bind(classOf[Pass])
      .annotatedWith(Names.named("InitialPass"))
      .to(classOf[SanyParserPass])

    // EtcTypeCheckerPassImpl
    bind(classOf[EtcTypeCheckerPass])
        .to(classOf[EtcTypeCheckerPassImpl])
    // the type checker is the next one after the parser
    bind(classOf[Pass])
        .annotatedWith(Names.named("AfterParser"))
        .to(classOf[EtcTypeCheckerPass])

    // the next pass after EtcTypeCheckerPass is the terminal pass
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterTypeChecker"))
      .to(classOf[TerminalPassWithTlaModule])
  }
}

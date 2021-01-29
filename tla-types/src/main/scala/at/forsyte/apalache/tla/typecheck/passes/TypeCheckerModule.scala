package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TerminalPassWithTlaModule, WriteablePassOptions}
import at.forsyte.apalache.io.annotations.AnnotationStoreProvider
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import com.google.inject.{AbstractModule, TypeLiteral}
import com.google.inject.name.Names

class TypeCheckerModule extends AbstractModule {

  override def configure(): Unit = {
    // the options singleton
    bind(classOf[PassOptions])
      .to(classOf[WriteablePassOptions])
    // exception handler
    bind(classOf[ExceptionAdapter])
      .to(classOf[EtcTypeCheckerAdapter])

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

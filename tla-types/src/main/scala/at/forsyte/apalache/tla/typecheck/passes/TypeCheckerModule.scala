package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TerminalPassWithTlaModule, WriteablePassOptions}
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.tla.lir.io.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
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

    // writers
    bind(classOf[TlaWriterFactory])
      .to(classOf[PrettyWriterWithAnnotationsFactory])

    // use the idle listener, as we do not need transformation tracking
    bind(classOf[TransformationTracker])
      .to(classOf[IdleTracker])
    bind(classOf[TransformationListener])
      .to(classOf[ChangeListener])

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

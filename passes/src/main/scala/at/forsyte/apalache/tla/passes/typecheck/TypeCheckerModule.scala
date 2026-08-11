package at.forsyte.apalache.tla.passes.typecheck

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{DerivedPredicates, Pass, ToolModule}
import at.forsyte.apalache.io.OutputWorkspace
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.config.{CommonOptions, ModuleIoOptions, TypecheckerOptions, ValidatedTypecheckOptions}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.passes.imp.{SanyParserPass, SanyParserPassImpl}
import com.google.inject.TypeLiteral

class TypeCheckerModule(options: ValidatedTypecheckOptions, outputWorkspace: OutputWorkspace) extends ToolModule {
  override def configure(): Unit = {
    bind(classOf[OutputWorkspace]).toInstance(outputWorkspace)
    bind(classOf[CommonOptions]).toInstance(options.common)
    bind(classOf[ModuleIoOptions]).toInstance(ModuleIoOptions(options.source, options.output))
    bind(classOf[TypecheckerOptions]).toInstance(options.typechecker)

    // The `DerivedPredicate` instance used to communicate specification predicates between passes
    val derivedPreds = DerivedPredicates.Impl()
    // Read-only access to the derivedPreds
    bind(classOf[DerivedPredicates]).toInstance(derivedPreds)
    // Writeable access to the derivedPreds
    bind(classOf[DerivedPredicates.Configurable]).toInstance(derivedPreds)

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

    // Bind all passes
    bind(classOf[SanyParserPass]).to(classOf[SanyParserPassImpl])
    bind(classOf[EtcTypeCheckerPass]).to(classOf[EtcTypeCheckerPassImpl])
  }

  override def passes: Seq[Class[_ <: Pass]] = {
    Seq(
        classOf[SanyParserPass],
        classOf[EtcTypeCheckerPassImpl],
    )
  }
}

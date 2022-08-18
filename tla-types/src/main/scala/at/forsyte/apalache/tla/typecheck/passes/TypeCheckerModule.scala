package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, ToolModule, WriteablePassOptions}
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import com.google.inject.TypeLiteral
import at.forsyte.apalache.infra.passes.options.OptionGroup

class TypeCheckerModule[O <: OptionGroup.HasTypechecker] extends ToolModule[O] {
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

    // Bind all passes
    bind(classOf[SanyParserPass]).to(classOf[SanyParserPassImpl])
    bind(classOf[EtcTypeCheckerPass]).to(classOf[EtcTypeCheckerPassImpl])

    super.configure()
  }

  override def passes: Seq[Class[_ <: Pass]] = {
    Seq(
        classOf[SanyParserPass],
        classOf[EtcTypeCheckerPassImpl],
    )
  }
}

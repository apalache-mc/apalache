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

class TypeCheckerModule(options: OptionGroup.HasTypechecker) extends ToolModule(options) {
  override def configure(): Unit = {
    // Set up the sub-trait hierarchy.
    // TODO This is mad, and must be replaced.
    // See https://stackoverflow.com/questions/31598703/does-guice-binding-bind-subclass-as-well
    bind(classOf[OptionGroup]).to(classOf[OptionGroup.HasCommon])
    bind(classOf[OptionGroup.HasCommon]).to(classOf[OptionGroup.HasInput])
    bind(classOf[OptionGroup.HasInput]).to(classOf[OptionGroup.HasIO])
    bind(classOf[OptionGroup.HasOutput]).to(classOf[OptionGroup.HasIO])
    bind(classOf[OptionGroup.HasIO]).to(classOf[OptionGroup.HasTypechecker])
    bind(classOf[OptionGroup.HasTypechecker]).toInstance(options)

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

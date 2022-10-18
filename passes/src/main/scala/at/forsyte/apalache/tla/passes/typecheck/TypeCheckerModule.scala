package at.forsyte.apalache.tla.passes.typecheck

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.{DerivedPredicates, Pass, ToolModule}
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import com.google.inject.TypeLiteral

class TypeCheckerModule(options: OptionGroup.HasTypechecker) extends ToolModule(options) {
  override def configure(): Unit = {
    // Ensure the given `options` will be bound to any OptionGroup interface
    // See https://stackoverflow.com/questions/31598703/does-guice-binding-bind-subclass-as-well
    // for why we cannot just specify the upper bound.
    bind(classOf[OptionGroup.HasCommon]).toInstance(options)
    bind(classOf[OptionGroup.HasInput]).toInstance(options)
    bind(classOf[OptionGroup.HasOutput]).toInstance(options)
    bind(classOf[OptionGroup.HasIO]).toInstance(options)
    bind(classOf[OptionGroup.HasTypechecker]).toInstance(options)

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

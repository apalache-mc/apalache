package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes._
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.assignments.passes._
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.passes._
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.pp.passes._
import com.google.inject.TypeLiteral
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.tla.passes.typecheck.EtcTypeCheckerPassImpl

/**
 * A configuration that binds all the passes from the parser to the checker. If you are not sure how the binding works,
 * check the tutorial on Google Guice.
 *
 * @author
 *   Igor Konnov
 */
class CheckerModule(options: OptionGroup.HasCheckerPreds) extends ToolModule(options) {

  override def configure(): Unit = {
    // Ensure the given `options` will be bound to any OptionGroup interface
    // See https://stackoverflow.com/questions/31598703/does-guice-binding-bind-subclass-as-well
    // for why we cannot just specify the upper bound.
    bind(classOf[OptionGroup.HasCommon]).toInstance(options)
    bind(classOf[OptionGroup.HasInput]).toInstance(options)
    bind(classOf[OptionGroup.HasOutput]).toInstance(options)
    bind(classOf[OptionGroup.HasIO]).toInstance(options)
    bind(classOf[OptionGroup.HasTypechecker]).toInstance(options)
    bind(classOf[OptionGroup.HasChecker]).toInstance(options)
    bind(classOf[OptionGroup.HasCheckerPreds]).toInstance(options)

    // The `DerivedPredicate` instance used to communicate specification predicates between passes
    val derivedPreds = DerivedPredicates.Impl()
    // Read-only access to the derivedPreds
    bind(classOf[DerivedPredicates]).toInstance(derivedPreds)
    // Writeable access to the derivedPreds
    bind(classOf[DerivedPredicates.Configurable]).toInstance(derivedPreds)

    // exception handler
    bind(classOf[ExceptionAdapter])
      .to(classOf[CheckerExceptionAdapter])

    // stores
    // Create an annotation store with the custom provider.
    // We have to use TypeLiteral, as otherwise Guice is getting confused by type erasure.
    bind(new TypeLiteral[AnnotationStore]() {})
      .toProvider(classOf[AnnotationStoreProvider])
    bind(classOf[ExprGradeStore])
      .to(classOf[ExprGradeStoreImpl])

    // writers
    bind(classOf[TlaWriterFactory])
      .to(classOf[PrettyWriterWithAnnotationsFactory])

    // transformation tracking
    // TODO: the binding of TransformationListener should disappear in the future
    bind(classOf[TransformationListener])
      .to(classOf[ChangeListener])
    // check TransformationTrackerProvider to find out which listeners the tracker is using
    bind(classOf[TransformationTracker])
      .toProvider(classOf[TransformationTrackerProvider])

    // Bind all passes
    bind(classOf[SanyParserPass]).to(classOf[SanyParserPassImpl])
    bind(classOf[ConfigurationPass]).to(classOf[ConfigurationPassImpl])
    bind(classOf[DesugarerPass]).to(classOf[DesugarerPassImpl])
    bind(classOf[TemporalPass]).to(classOf[TemporalPassImpl])
    bind(classOf[InlinePass]).to(classOf[InlinePassImpl])
    bind(classOf[PrimingPass]).to(classOf[PrimingPassImpl])
    bind(classOf[VCGenPass]).to(classOf[VCGenPassImpl])
    bind(classOf[PreproPass]).to(classOf[PreproPassImpl])
    bind(classOf[TransitionPass]).to(classOf[TransitionPassImpl])
    bind(classOf[OptPass]).to(classOf[OptPassImpl])
    bind(classOf[AnalysisPass]).to(classOf[AnalysisPassImpl])
    bind(classOf[BoundedCheckerPass]).to(classOf[BoundedCheckerPassImpl])
  }

  override def passes: Seq[Class[_ <: Pass]] = {
    Seq(
        classOf[SanyParserPass],
        // The next pass is Snowcat that is called EtcTypeCheckerPassImpl for now.
        // We use a concrete implementation here, as we also do with PostTypeCheckerPassImpl later in the pipeline.
        classOf[EtcTypeCheckerPassImpl],
        classOf[ConfigurationPass],
        classOf[DesugarerPass],
        classOf[InlinePass],
        classOf[TemporalPass],
        classOf[InlinePass],
        classOf[PrimingPass],
        classOf[VCGenPass],
        classOf[PreproPass],
        classOf[TransitionPass],
        classOf[OptPass],
        classOf[AnalysisPass],
        // BoundedCheckerPass is in the very end of the pipeline
        classOf[BoundedCheckerPass],
    )
  }

}

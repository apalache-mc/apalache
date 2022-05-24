package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes._
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.tla.assignments.passes._
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.passes._
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.pp.passes._
import at.forsyte.apalache.tla.typecheck.passes.EtcTypeCheckerPassImpl
import com.google.inject.TypeLiteral

/**
 * A configuration that binds all the passes from the parser to the checker. If you are not sure how the binding works,
 * check the tutorial on Google Guice.
 *
 * @author
 *   Igor Konnov
 */
class CheckerModule extends ToolModule {
  override def configure(): Unit = {
    // the options singleton
    bind(classOf[PassOptions])
      .to(classOf[WriteablePassOptions])
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
        classOf[PrimingPass],
        classOf[VCGenPass],
        classOf[PreproPass],
        classOf[TransitionPass],
        classOf[OptPass],
        classOf[AnalysisPass],
        // do the final type checking again, as preprocessing may have introduced gaps in the expression types
        classOf[PostTypeCheckerPassImpl],
        // BoundedCheckerPass is in the very end of the pipeline
        classOf[BoundedCheckerPass],
    )
  }

}

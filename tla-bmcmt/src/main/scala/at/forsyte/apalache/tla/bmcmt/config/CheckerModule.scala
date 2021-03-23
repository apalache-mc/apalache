package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes._
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.tla.assignments.passes._
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.passes._
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.tla.lir.io.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.pp.passes._
import at.forsyte.apalache.tla.typecheck.passes.{EtcTypeCheckerPass, EtcTypeCheckerPassImpl}
import com.google.inject.name.Names
import com.google.inject.{AbstractModule, TypeLiteral}

/**
 * A configuration that binds all the passes from the parser to the checker.
 * If you are not sure how the binding works, check the tutorial on Google Guice.
 *
 * @author Igor Konnov
 */
class CheckerModule extends AbstractModule {
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
    bind(classOf[FormulaHintsStore])
      .to(classOf[FormulaHintsStoreImpl])
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

    // SanyParserPassImpl is the default implementation of SanyParserPass
    bind(classOf[SanyParserPass])
      .to(classOf[SanyParserPassImpl])
    // and it also the initial pass for PassChainExecutor
    bind(classOf[Pass])
      .annotatedWith(Names.named("InitialPass"))
      .to(classOf[SanyParserPass])

    // The next pass is Snowcat that is called EtcTypeCheckerPassImpl for now.
    // We provide guice with a concrete implementation here, as we also use PostTypeCheckerPassImpl later in the pipeline.
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterParser"))
      .to(classOf[EtcTypeCheckerPassImpl])

    // the next pass is ConfigurationPass
    bind(classOf[ConfigurationPass])
      .to(classOf[ConfigurationPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterTypeChecker"))
      .to(classOf[ConfigurationPass])

    // the next pass is DesugarerPass
    bind(classOf[DesugarerPass])
      .to(classOf[DesugarerPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterConfiguration"))
      .to(classOf[DesugarerPass])
    // the next pass is UnrollPass
    bind(classOf[UnrollPass])
      .to(classOf[UnrollPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterDesugarer"))
      .to(classOf[UnrollPass])
    // the next pass is PrimingPass
    bind(classOf[PrimingPass])
      .to(classOf[PrimingPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterUnroll"))
      .to(classOf[PrimingPass])
    // the next pass is CoverAnalysisPass
    bind(classOf[CoverAnalysisPass])
      .to(classOf[CoverAnalysisPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterPriming"))
      .to(classOf[CoverAnalysisPass])
    // the next pass is InlinePass
    bind(classOf[InlinePass])
      .to(classOf[InlinePassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterCoverAnalysis"))
      .to(classOf[InlinePass])
    // the next pass is VCGenPass
    bind(classOf[VCGenPass])
      .to(classOf[VCGenPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterInline"))
      .to(classOf[VCGenPass])
    // the next pass after SanyParserPass is PreproPass
    bind(classOf[PreproPass])
      .to(classOf[PreproPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterVCGen"))
      .to(classOf[PreproPass])
    // the next pass after PreproPass is AssignmentPass
    bind(classOf[TransitionPass])
      .to(classOf[TransitionPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterPrepro"))
      .to(classOf[TransitionPass])
    // the next pass after AssignmentPass is AnalysisPass
    bind(classOf[OptPass])
      .to(classOf[OptPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterTransitionFinder"))
      .to(classOf[OptPass])
    // the next pass after AssignmentPass is AnalysisPass
    bind(classOf[AnalysisPass])
      .to(classOf[AnalysisPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterOpt"))
      .to(classOf[AnalysisPass])

    // do the final type checking again, as preprocessing may have introduced gaps in the expression types
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterAnalysis"))
      .to(classOf[PostTypeCheckerPassImpl])

    // BoundedCheckerPass is in the very end of the pipeline
    bind(classOf[BoundedCheckerPass])
      .to(classOf[BoundedCheckerPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterPostTypeChecker"))
      .to(classOf[BoundedCheckerPass])

    // the final pass is TerminalPass
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterChecker"))
      .to(classOf[TerminalPass])
  }

}

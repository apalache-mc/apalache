package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.{DefaultExceptionAdapter, ExceptionAdapter}
import at.forsyte.apalache.infra.passes._
import at.forsyte.apalache.tla.assignments.passes._
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.passes._
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.bmcmt.types.{CellT, TypeFinder}
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.pp.passes._
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
    bind(classOf[FormulaHintsStore])
      .to(classOf[FormulaHintsStoreImpl])
    bind(classOf[ExprGradeStore])
      .to(classOf[ExprGradeStoreImpl])
    bind(new TypeLiteral[TypeFinder[CellT]] {})
      .to(classOf[TrivialTypeFinder])   // using a trivial type finder

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
    // the next pass is ConfigurationPass
    bind(classOf[ConfigurationPass])
      .to(classOf[ConfigurationPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterParser"))
      .to(classOf[ConfigurationPass])
    // the next pass is UnrollPass
    bind(classOf[UnrollPass])
      .to(classOf[UnrollPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterConfiguration"))
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
    // the next pass after CoverAnalysisPass is AssignmentPass
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
    // the next pass after SimpleSkolemizationPass is BoundedCheckerPass
    bind(classOf[BoundedCheckerPass])
      .to(classOf[BoundedCheckerPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterAnalysis"))
      .to(classOf[BoundedCheckerPass])
    // the final pass is TerminalPass
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterChecker"))
      .to(classOf[TerminalPass])
  }

}

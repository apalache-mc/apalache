package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.infra.{ExitCodes, PassOptionException}
import at.forsyte.apalache.infra.passes.FineTuningParser
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.assignments.ModuleAdapter
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.analyses.ExprGradeStore
import at.forsyte.apalache.tla.bmcmt.rewriter.{MetricProfilerListener, RewriterConfig}
import at.forsyte.apalache.tla.bmcmt.search._
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.bmcmt.trex._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.LanguageWatchdog
import at.forsyte.apalache.tla.lir.transformations.standard.{
  IncrementalRenaming, KeraLanguagePred, MonotypeLanguagePred,
}
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.{Algorithm, OptionGroup}

/**
 * The implementation of a bounded model checker with SMT.
 *
 * @author
 *   Igor Konnov
 */
class BoundedCheckerPassImpl @Inject() (
    options: OptionGroup.HasChecker,
    exprGradeStore: ExprGradeStore,
    sourceStore: SourceStore,
    changeListener: ChangeListener,
    renaming: IncrementalRenaming)
    extends BoundedCheckerPass with LazyLogging {

  override def name: String = "BoundedChecker"

  override def execute(module: TlaModule): PassResult = {
    LanguageWatchdog(KeraLanguagePred()).check(module)
    LanguageWatchdog(MonotypeLanguagePred()).check(module)

    val initTrans = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.INIT_PREFIX)
    val nextTrans = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.NEXT_PREFIX)
    val cinitP = ModuleAdapter.getOperatorOption(module, NormalizedNames.CONST_INIT)
    val vcInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_INV_PREFIX)
    val vcNotInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_NOT_INV_PREFIX)
    val invariantsAndNegations = vcInvs.zip(vcNotInvs)
    val vcActionInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_ACTION_INV_PREFIX)
    val vcNotActionInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_NOT_ACTION_INV_PREFIX)
    val actionInvariantsAndNegations = vcActionInvs.zip(vcNotActionInvs)
    val vcTraceInvs = module.operDeclarations.filter(d => d.name.startsWith(NormalizedNames.VC_TRACE_INV_PREFIX))
    val vcNotTraceInvs = module.operDeclarations.filter(d => d.name.startsWith(NormalizedNames.VC_NOT_TRACE_INV_PREFIX))
    val traceInvariantsAndNegations = vcTraceInvs.zip(vcNotTraceInvs)
    val optView = module.operDeclarations.find(_.name == NormalizedNames.VC_VIEW).map(_.body)

    val verificationConditions =
      CheckerInputVC(invariantsAndNegations.toList, actionInvariantsAndNegations.toList,
          traceInvariantsAndNegations.toList, optView)
    val input = new CheckerInput(module, initTrans.toList, nextTrans.toList, cinitP, verificationConditions)
    val stepsBound = options.checker.length
    val debug = options.common.debug
    val tuning = options.checker.tuning
    // TODO: default smtEncoding option is needed here for executions with TestCmd, add encoding option to TestCmd instead
    val smtEncoding = options.checker.smtEncoding

    val params = new ModelCheckerParams(input, stepsBound, tuning)
    params.discardDisabled = options.checker.discardDisabled
    params.checkForDeadlocks = !options.checker.noDeadlocks
    params.nMaxErrors = options.checker.maxError
    params.timeoutSmtSec = options.checker.timeoutSmtSec
    params.smtEncoding = smtEncoding

    val smtProfile = options.common.smtprof
    val smtRandomSeed = tuning.getOrElse("smt.randomSeed", "0").toInt
    val smtStatsSec =
      tuning.getOrElse("smt.statsSec", SolverConfig.default.z3StatsSec.toString).toInt
    // Parse the tuning parameters that are relevant to Z3.
    // Currently, `tuning` may contain more configuration options (added by some passes) than we parse in
    // `FineTuningParser`.
    val z3Parameters = FineTuningParser.fromStrings(tuning.filter(_._1.startsWith("z3."))) match {
      case Right(params) => params.map { case (k, v) => (k.substring("z3.".length), v) }
      case Left(error)   => throw new PassOptionException(s"Error in tuning parameters: $error")
    }
    val solverConfig = SolverConfig(debug, smtProfile, smtRandomSeed, smtEncoding, smtStatsSec, z3Parameters)

    val result = options.checker.algo match {
      case Algorithm.Incremental => runIncrementalChecker(params, input, tuning, solverConfig)
      case Algorithm.Offline     => runOfflineChecker(params, input, tuning, solverConfig)
    }

    if (result.isOk) {
      Right(module)
    } else {
      passFailure(result, ExitCodes.ERROR_COUNTEREXAMPLE)
    }
  }

  private def runIncrementalChecker(
      params: ModelCheckerParams,
      input: CheckerInput,
      tuning: Map[String, String],
      solverConfig: SolverConfig): Checker.CheckerResult = {
    val solverContext: RecordingSolverContext = RecordingSolverContext.createZ3(None, solverConfig)

    val metricProfilerListener =
      if (solverConfig.profile) {
        logger.info("Profiling data will be written to profile.csv")
        Some(new MetricProfilerListener(sourceStore, changeListener))
      } else {
        None
      }

    val rewriter: SymbStateRewriterImpl = params.smtEncoding match {
      case SMTEncoding.OOPSLA19 =>
        new SymbStateRewriterImpl(solverContext, renaming, exprGradeStore, metricProfilerListener)
      case SMTEncoding.Arrays =>
        new SymbStateRewriterImplWithArrays(solverContext, renaming, exprGradeStore, metricProfilerListener)
      case SMTEncoding.FunArrays =>
        new SymbStateRewriterImplWithFunArrays(solverContext, renaming, exprGradeStore, metricProfilerListener)
      case oddEncoding => throw new IllegalArgumentException(s"Unexpected checker.smt-encoding=$oddEncoding")
    }

    rewriter.config = RewriterConfig(tuning)

    type SnapshotT = IncrementalExecutionContextSnapshot
    val executorContext = new IncrementalExecutionContext(rewriter)
    val trex =
      new TransitionExecutorImpl[SnapshotT](params.consts, params.vars, executorContext)
    val filteredTrex =
      new FilteredTransitionExecutor[SnapshotT](params.transitionFilter, params.invFilter, trex)

    val checker =
      new SeqModelChecker[SnapshotT](params, input, filteredTrex, Seq(DumpFilesModelCheckerListener))
    val outcome = checker.run()
    filteredTrex.dispose()
    logger.info(s"The outcome is: " + outcome)
    outcome
  }

  private def runOfflineChecker(
      params: ModelCheckerParams,
      input: CheckerInput,
      tuning: Map[String, String],
      solverConfig: SolverConfig): Checker.CheckerResult = {
    val solverContext: RecordingSolverContext = RecordingSolverContext.createZ3(None, solverConfig)

    if (solverConfig.profile) {
      logger.warn("SMT profiling is enabled, but offline SMT is used. No profiling data will be written.")
    }

    val rewriter: SymbStateRewriterImpl = params.smtEncoding match {
      case SMTEncoding.OOPSLA19 =>
        new SymbStateRewriterImpl(solverContext, renaming, exprGradeStore)
      case SMTEncoding.Arrays =>
        new SymbStateRewriterImplWithArrays(solverContext, renaming, exprGradeStore)
      case SMTEncoding.FunArrays =>
        new SymbStateRewriterImplWithFunArrays(solverContext, renaming, exprGradeStore)
      case oddEncoding => throw new IllegalArgumentException(s"Unexpected checker.smt-encoding=$oddEncoding")
    }
    rewriter.config = RewriterConfig(tuning)

    type SnapshotT = OfflineExecutionContextSnapshot
    val executorContext = new OfflineExecutionContext(rewriter, renaming)
    val trex = new TransitionExecutorImpl[SnapshotT](params.consts, params.vars, executorContext)
    val filteredTrex = new FilteredTransitionExecutor[SnapshotT](params.transitionFilter, params.invFilter, trex)

    val checker =
      new SeqModelChecker[SnapshotT](params, input, filteredTrex, Seq(DumpFilesModelCheckerListener))
    val outcome = checker.run()
    executorContext.dispose()
    logger.info(s"The outcome is: " + outcome)
    outcome
  }

  /*
  TODO: the following code will be uncommented when the paralel checker is transferred from ik/multicore

  private def runParallelChecker(params: ModelCheckerParams,
                                 input: CheckerInput,
                                 tuning: Map[String, String],
                                 nworkers: Int): Boolean = {
    val sharedState = new SharedSearchState(nworkers)

    def createCheckerThread(rank: Int): Thread = {
      new Thread {
        override def run(): Unit = {
          try {
            val checker = createParallelWorker(rank, sharedState, params, input, tuning)
            val outcome = checker.run()
            logger.info(s"Worker $rank: The outcome is: $outcome")
          } catch {
            case e: Exception if exceptionAdapter.toMessage.isDefinedAt(e) =>
              val message = exceptionAdapter.toMessage(e)
              logger.info(s"Worker $rank: The outcome is: Error")
              logger.error("Worker %s: %s".format(rank, message))

            case e: Throwable =>
              logger.error(s"Worker $rank has thrown an exception", e)
              System.exit(EXITCODE_ON_EXCEPTION)
          }
        }
      }
    }

    // run the threads and join
    val workerThreads = 1.to(nworkers) map createCheckerThread
    val shutdownHook = createShutdownHook(workerThreads)
    Runtime.getRuntime.addShutdownHook(shutdownHook)    // shutdown the threads, if needed
    workerThreads.foreach(_.start())                    // start the workers
    workerThreads.foreach(_.join())                     // wait for their termination
    Runtime.getRuntime.removeShutdownHook(shutdownHook) // no need for the hook anymore

    sharedState.workerStates.values.forall(_ == BugFreeState())
  }

  private def createParallelWorker(rank: Int,
                                 sharedState: SharedSearchState,
                                 params: ModelCheckerParams,
                                 input: CheckerInput,
                                 tuning: Map[String, String]): ParModelChecker = {
    val profile = options.getOrElse("smt", "prof", false)
    val solverContext: RecordingZ3SolverContext = RecordingZ3SolverContext(None, params.debug, profile)

    val typeFinder = new TrivialTypeFinder
    val rewriter: SymbStateRewriterImpl = params.smtEncoding match {
      case SMTEncoding.OOPSLA19  => new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)
      case SMTEncoding.Arrays    => new SymbStateRewriterImplWithArrays(solverContext, typeFinder, exprGradeStore)
      case SMTEncoding.FunArrays => new SymbStateRewriterImplWithFunArrays(solverContext, typeFinder, exprGradeStore)
      case oddEncoding           => throw new IllegalArgumentException(s"Unexpected checker.smt-encoding=$oddEncoding")
    }
    rewriter.formulaHintsStore = hintsStore
    rewriter.config = RewriterConfig(tuning)

    val executorContext = new OfflineExecutorContext(rewriter)
    val trex = new TransitionExecutorImpl[OfflineSnapshot](params.consts, params.vars, executorContext)
    val filteredTrex = new FilteredTransitionExecutor[OfflineSnapshot](params.transitionFilter, params.invFilter, trex)
    val context = new WorkerContext(rank, sharedState.searchRoot, filteredTrex)

    new ParModelChecker(input, params, sharedState, context)
  }

  private def createShutdownHook(workerThreads: Seq[Thread]): Thread = {
    new Thread() {
      override def run(): Unit = {
        logger.error("Shutdown hook activated. Interrupting the workers and joining them for %d ms."
          .format(JOIN_TIMEOUT_MS))
        workerThreads.foreach(_.interrupt())
        workerThreads.foreach(_.join(JOIN_TIMEOUT_MS))
        logger.error("Forced shutdown")
        Runtime.getRuntime.halt(EXITCODE_ON_SHUTDOWN)
      }
    }
  }
   */

  override def dependencies = Set(ModuleProperty.Analyzed)

  override def transformations = Set()
}

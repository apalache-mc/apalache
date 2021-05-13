package at.forsyte.apalache.tla.bmcmt.passes

import java.nio.file.Path
import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.ModuleAdapter
import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FormulaHintsStore}
import at.forsyte.apalache.tla.bmcmt.rewriter.{MetricProfilerListener, RewriterConfig}
import at.forsyte.apalache.tla.bmcmt.search._
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.bmcmt.trex._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.NullEx
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.LanguageWatchdog
import at.forsyte.apalache.tla.lir.transformations.standard.KeraLanguagePred
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.File

/**
 * The implementation of a bounded model checker with SMT.
 *
 * @author Igor Konnov
 */
class BoundedCheckerPassImpl @Inject() (val options: PassOptions, hintsStore: FormulaHintsStore,
    exprGradeStore: ExprGradeStore, sourceStore: SourceStore, changeListener: ChangeListener,
    @Named("AfterChecker") nextPass: Pass)
    extends BoundedCheckerPass with LazyLogging {

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  override def name: String = "BoundedChecker"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized", NullEx)
    }
    val module = tlaModule.get

    for (decl <- module.operDeclarations) {
      LanguageWatchdog(KeraLanguagePred()).check(decl.body)
    }

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

    val verificationConditions =
      CheckerInputVC(invariantsAndNegations.toList, actionInvariantsAndNegations.toList,
          traceInvariantsAndNegations.toList)
    val input = new CheckerInput(module, initTrans.toList, nextTrans.toList, cinitP, verificationConditions)
    /*
        TODO: uncomment when the parallel checker is transferred from ik/multicore
    val nworkers = options.getOrElse("checker", "nworkers", 1)
     */
    val stepsBound = options.getOrElse("checker", "length", 10)
    val tuning = options.getOrElse("general", "tuning", Map[String, String]())
    val debug = options.getOrElse("general", "debug", false)
    val saveDir = options.getOrError("io", "outdir").asInstanceOf[Path].toFile

    val params = new ModelCheckerParams(input, stepsBound, saveDir, tuning, debug)
    params.discardDisabled = options.getOrElse("checker", "discardDisabled", true)
    params.checkForDeadlocks = !options.getOrElse("checker", "noDeadlocks", false)

    val smtProfile = options.getOrElse("smt", "prof", false)
    val smtRandomSeed = tuning.getOrElse("smt.randomSeed", "0").toInt
    val solverConfig = SolverConfig(debug, smtProfile, smtRandomSeed)

    options.getOrElse("checker", "algo", "incremental") match {
      /*
        TODO: uncomment when the parallel checker is transferred from ik/multicore
      case "parallel" => runParallelChecker(params, input, tuning, nworkers)
       */
      case "incremental" => runIncrementalChecker(params, input, tuning, solverConfig)
      case "offline"     => runOfflineChecker(params, input, tuning, solverConfig)
      case algo          => throw new IllegalArgumentException(s"Unexpected checker.algo=$algo")
    }

  }

  private def runIncrementalChecker(params: ModelCheckerParams, input: CheckerInput, tuning: Map[String, String],
      solverConfig: SolverConfig): Boolean = {
    val solverContext: RecordingSolverContext = RecordingSolverContext.createZ3(None, solverConfig)

    val metricProfilerListener =
      if (solverConfig.profile) {
        logger.info("Profiling data will be written to profile.csv")
        Some(new MetricProfilerListener(sourceStore, changeListener, new File("profile.csv")))
      } else {
        None
      }

    val rewriter: SymbStateRewriterImpl =
      new SymbStateRewriterImpl(solverContext, exprGradeStore, metricProfilerListener)

    rewriter.formulaHintsStore = hintsStore
    rewriter.config = RewriterConfig(tuning)

    type SnapshotT = IncrementalExecutionContextSnapshot
    val executorContext = new IncrementalExecutionContext(rewriter)
    val trex =
      new TransitionExecutorImpl[SnapshotT](params.consts, params.vars, executorContext)
    val filteredTrex =
      new FilteredTransitionExecutor[SnapshotT](params.transitionFilter, params.invFilter, trex)

    val checker = new SeqModelChecker[SnapshotT](params, input, filteredTrex)
    val outcome = checker.run()
    logger.info(s"The outcome is: " + outcome)
    outcome == Outcome.NoError
  }

  private def runOfflineChecker(params: ModelCheckerParams, input: CheckerInput, tuning: Map[String, String],
      solverConfig: SolverConfig): Boolean = {
    val solverContext: RecordingSolverContext = RecordingSolverContext.createZ3(None, solverConfig)

    if (solverConfig.profile) {
      logger.warn("SMT profiling is enabled, but offline SMT is used. No profiling data will be written.")
    }

    val rewriter: SymbStateRewriterImpl = new SymbStateRewriterImpl(solverContext, exprGradeStore)
    rewriter.formulaHintsStore = hintsStore
    rewriter.config = RewriterConfig(tuning)

    type SnapshotT = OfflineExecutionContextSnapshot
    val executorContext = new OfflineExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl[SnapshotT](params.consts, params.vars, executorContext)
    val filteredTrex = new FilteredTransitionExecutor[SnapshotT](params.transitionFilter, params.invFilter, trex)

    val checker = new SeqModelChecker[SnapshotT](params, input, filteredTrex)
    val outcome = checker.run()
    logger.info(s"The outcome is: " + outcome)
    outcome == Outcome.NoError
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
    val rewriter: SymbStateRewriterImpl = new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)
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

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] =
    tlaModule map { _ => nextPass }
}

package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.Algorithm.Remote
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import at.forsyte.apalache.infra.passes.options.OptionGroup.{HasCheckerPreds, WithCheckerPreds}
import at.forsyte.apalache.infra.passes.options.SMTEncoding.OOPSLA19
import at.forsyte.apalache.infra.passes.options.{Config, SourceOption}
import at.forsyte.apalache.infra.tlc.config.InitNextSpec
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.io.lir.{ItfCounterexampleWriter, Trace}
import at.forsyte.apalache.tla.bmcmt.ModelCheckerContext
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl
import at.forsyte.apalache.tla.bmcmt.trex.IncrementalExecutionContextSnapshot
import com.fasterxml.jackson.databind.node.{NullNode, ObjectNode}
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import com.google.inject.Injector
import com.typesafe.scalalogging.LazyLogging
import jakarta.servlet.annotation.WebServlet
import jakarta.servlet.http.{HttpServlet, HttpServletRequest, HttpServletResponse}
import org.eclipse.jetty.server.Server
import org.eclipse.jetty.servlet.{ServletContextHandler, ServletHolder}

import java.io.StringReader
import java.util.concurrent.{LinkedBlockingQueue, ThreadPoolExecutor, TimeUnit}
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.concurrent.TrieMap
import scala.collection.immutable
import scala.collection.immutable.SortedSet
import scala.util.Try

/**
 * An error that can occur in the exploration service.
 * @param code
 *   error code, typically a JSON-RPC error code
 * @param message
 *   a human-readable error message
 */
case class ServiceError(code: Int, message: String)

/**
 * A transition exploration service.
 * @param config
 *   the service configuration, typically, constructed with [[at.forsyte.apalache.io.ConfigManager]].
 */
class ExplorationService(config: Try[Config.ApalacheConfig]) extends LazyLogging {
  // Guice injector instantiated for each session. This injector contains objects that are
  // configured via CheckerModule. Instead of doing model checking, it just prepares
  // ModelCheckerContext in the `remote` mode. We are using TrieMap to allow concurrent reads and updates.
  private val sessions: TrieMap[String, Injector] = TrieMap.empty
  // A counter for generating session IDs.
  private val lastSessionId: AtomicInteger = new AtomicInteger(0)
  // A snapshot manager.
  private val snapshots: CheckerSnapshotsPerSession = new CheckerSnapshotsPerSession()

  /**
   * Loads a specification based on the provided parameters.
   * @param params
   *   parsed loading parameters
   * @return
   */
  def loadSpec(params: LoadSpecParams): Either[ServiceError, LoadSpecResult] = {
    val sessionId = lastSessionId.incrementAndGet().toHexString
    logger.info(s"Session $sessionId: Loading specification with ${params.sources.length} sources.")
    val options = createConfigFromParams(params).get
    // call the parser
    val passChainExecutor = PassChainExecutor(new CheckerModule(options))
    passChainExecutor.run() match {
      case Left(failure) =>
        return Left(ServiceError(failure.exitCode, s"Failed to load specification: $failure"))
      case Right(_) =>
        // Successfully loaded the spec, we can access the module later
        sessions.put(sessionId, passChainExecutor.injector)
    }
    // get the singleton instance of BoundedModelCheckerPass from checker
    val checkerModule = passChainExecutor.injector.getInstance(classOf[BoundedCheckerPassImpl])
    val checkerContext = checkerModule.modelCheckerContext.get
    val checkerInput = checkerContext.checkerInput
    // initialize CONSTANTS
    if (checkerContext.checkerInput.constInitPrimed.isDefined) {
      checkerContext.trex.initializeConstants(checkerContext.checkerInput.constInitPrimed.get)
    }
    // propagate constraints from ASSUME(...)
    checkerContext.checkerInput.rootModule.assumeDeclarations.foreach { d =>
      checkerContext.trex.assertState(d.body)
    }
    // save the snapshot of the checker context
    val snapshotId = snapshots.takeSnapshot(sessionId, checkerContext)

    // produce the specification parameters for remote exploration
    val specParameters = SpecParameters(
        nInitTransitions = checkerInput.initTransitions.size,
        nNextTransitions = checkerInput.nextTransitions.size,
        nStateInvariants = checkerInput.verificationConditions.stateInvariantsAndNegations.size,
        nActionInvariants = checkerInput.verificationConditions.actionInvariantsAndNegations.size,
        hasView = checkerInput.verificationConditions.stateView.nonEmpty,
    )

    logger.info(s"Session=$sessionId Step=0 Snapshot=$snapshotId: Specification ready")

    Right(LoadSpecResult(sessionId, snapshotId, specParameters))
  }

  /**
   * Dispose a previously loaded specification by its session ID.
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[DisposeSpecResult]]
   */
  def disposeSpec(params: DisposeSpecParams): Either[ServiceError, DisposeSpecResult] = {
    val result =
      sessions.get(params.sessionId) match {
        case Some(injector) =>
          // immediately remove the session, so the other threads would start anything on it
          sessions.remove(params.sessionId)
          snapshots.remove(params.sessionId)
          // get the checker context from the injector
          val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
          val checkerContext = checkerModule.modelCheckerContext
          // lock on the checker context, so we do not access the SMT context concurrently
          checkerContext.synchronized {
            checkerContext.foreach(_.trex.dispose())
          }
          logger.info(s"Session ${params.sessionId}: Disposed.")
          Right(DisposeSpecResult(params.sessionId))
        case None =>
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Session not found: ${params.sessionId}"))
      }

    result
  }

  /**
   * Prepare a symbolic transition in the solver context.
   *
   * @param params
   *   the parameters object that contains the session ID and the transition ID
   * @return
   *   either an error or [[AssumeTransitionResult]]
   */
  def assumeTransition(params: AssumeTransitionParams): Either[ServiceError, AssumeTransitionResult] = {
    val transitionId = params.transitionId
    val sessionId = params.sessionId
    // validate the input parameters
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        // we can only check obvious issues with transition ID here, as the step number
        // may change after snapshot recovery
        if (transitionId < 0) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Invalid transition ID: $transitionId must be non-negative"))
        } else {
          Right(checkerContext)
        }

      case None =>
        Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Session not found: $sessionId"))
    }

    // Prepare the transition. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map { checkerContext =>
        {
          checkerContext.synchronized {
            var snapshotBeforeId: Integer = -1
            if (params.snapshotId >= 0) {
              // try to recover the snapshot
              val recovered = snapshots.recoverSnapshot(sessionId, checkerContext, params.snapshotId)
              if (!recovered) {
                return Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                        s"Snapshot not found: ${params.snapshotId} in session $sessionId"))
              }
              snapshotBeforeId = params.snapshotId
            } else {
              // take a snapshot of the current context
              snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
            }
            // the step number might have changed after recovery, so we re-fetch the transitions
            val stepNo = checkerContext.trex.stepNo
            val transitions = if (stepNo == 0) {
              checkerContext.checkerInput.initTransitions
            } else {
              checkerContext.checkerInput.nextTransitions
            }
            if (transitionId < 0 || transitionId >= transitions.size) {
              return Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                      s"Invalid transition ID: $transitionId not in [0, ${transitions.size})"))
            }
            val actionExpr = transitions(transitionId)
            // Upload the transition into the SMT context.
            // It returns the result of a simple check that does not check satisfiability.
            val isApplicable = checkerContext.trex.prepareTransition(transitionId, actionExpr)
            if (!isApplicable) {
              snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
              logger.info(
                  s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: transition $transitionId DISABLED")
              AssumeTransitionResult(sessionId, snapshotBeforeId, transitionId, TransitionStatus.DISABLED)
            } else {
              // assume that this transition takes place
              checkerContext.trex.assumeTransition(transitionId)
              val snapshotAfterId = snapshots.takeSnapshot(sessionId, checkerContext)
              if (!params.checkEnabled) {
                // if we do not check satisfiability, we assume that the transition is enabled
                logger.info(
                    s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
                AssumeTransitionResult(sessionId, snapshotAfterId, transitionId, TransitionStatus.UNKNOWN)
              } else {
                // check satisfiability
                checkerContext.trex.sat(params.timeoutSec) match {
                  case Some(isSat) =>
                    if (!isSat) {
                      snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
                    }
                    val status = if (isSat) TransitionStatus.ENABLED else TransitionStatus.DISABLED
                    logger.info(
                        s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId $status")
                    AssumeTransitionResult(sessionId, snapshotBeforeId, transitionId, status)
                  case None =>
                    // in case of timeout or unknown, we do not rollback the context, but return unknown
                    logger.info(
                        s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
                    AssumeTransitionResult(sessionId, snapshotAfterId, transitionId, TransitionStatus.UNKNOWN)
                }
              }
            }
          }
        }
      }
  }

  /**
   * Switch to the next step.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[NextStepResult]]
   */
  def nextStep(params: NextStepParams): Either[ServiceError, NextStepResult] = {
    val sessionId = params.sessionId
    // validate the input parameters under the global lock
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        Right(checkerContext)

      case None =>
        Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Session not found: $sessionId"))
    }

    // Roll to the next step. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map { checkerContext =>
        {
          checkerContext.synchronized {
            val stepBeforeNo = checkerContext.trex.stepNo
            checkerContext.trex.nextState()
            val stepAfterNo = checkerContext.trex.stepNo
            val snapshotId = snapshots.takeSnapshot(sessionId, checkerContext)
            logger.info(s"Session=$sessionId Step=$stepAfterNo Snapshot=$snapshotId: Switched from step $stepBeforeNo")
            NextStepResult(sessionId, snapshotId, stepAfterNo)
          }
        }
      }
  }

  /**
   * Check the invariants against the current SMT context.
   * @param params
   *   checking parameters
   * @return
   *   either an error or the checking result
   */
  def checkInvariant(params: CheckInvariantParams): Either[ServiceError, CheckInvariantResult] = {
    val sessionId = params.sessionId
    val invariantId = params.invariantId
    // validate the input parameters
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        // check the invariant IDs, so we don't have to waste compute on obvious errors
        val nStateInvs = checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations.size
        val nActionInvs = checkerContext.checkerInput.verificationConditions.actionInvariantsAndNegations.size
        if (invariantId >= nStateInvs + nActionInvs) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid invariant ID: $invariantId not in [0, ${nStateInvs + nActionInvs})"))
        } else {
          Right(checkerContext)
        }

      case None =>
        Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Session not found: $sessionId"))
    }

    // Check the invariant
    validationResult.map { checkerContext =>
      checkerContext.synchronized {
        // take a snapshot of the current context
        val snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
        // if it's too early to check a state or action invariant, return SATISFIED
        val stepNo = checkerContext.trex.stepNo
        val nStateInvs = checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations.size
        val isStateInv = invariantId < nStateInvs
        if (stepNo == 0 || stepNo == 1 && !isStateInv) {
          // stepNo == 0 => Init has not been applied, so no state invariant can be violated
          // stepNo == 1 => only Init has been applied, so no action invariant can be violated
          logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: invariant $invariantId SATISFIED")
          return Right(CheckInvariantResult(sessionId, InvariantStatus.SATISFIED, NullNode.getInstance()))
        }
        // extract the corresponding invariant negation
        val notInvExpr =
          if (isStateInv) {
            // state invariant
            checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations(invariantId)._2
          } else {
            // action invariant
            val actionInvId = invariantId - nStateInvs
            checkerContext.checkerInput.verificationConditions.actionInvariantsAndNegations(actionInvId)._2
          }
        // assert the negation of the invariant
        checkerContext.trex.assertState(notInvExpr)
        // ...and check whether the negation is satisfiable
        val (status, jsonTrace) =
          checkerContext.trex.sat(params.timeoutSec) match {
            case Some(isSat) =>
              if (isSat) {
                val counterexample = getTrace(checkerContext)
                // Serialize the counterexample to JSON
                val ujsonTrace =
                  ItfCounterexampleWriter.mkJson(checkerContext.checkerInput.rootModule, counterexample.states)
                // Unfortunately, ujsonTrace is in UJSON, and we need Jackson's JsonNode.
                val jacksonNode =
                  new ObjectMapper().registerModule(DefaultScalaModule).readTree(new StringReader(ujsonTrace.render()))
                (InvariantStatus.VIOLATED, jacksonNode)
              } else {
                (InvariantStatus.SATISFIED, NullNode.getInstance())
              }

            case None =>
              (InvariantStatus.UNKNOWN, NullNode.getInstance())
          }
        // recover the snapshot
        snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
        logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: invariant $invariantId $status")
        CheckInvariantResult(sessionId, status, jsonTrace)
      }
    }
  }

  /**
   * Extract a trace from the transition executor.
   *
   * @return
   *   a trace with the data attached
   */
  private def getTrace(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot]): Trace[Unit] = {
    // We do not extract any labels. The remote client should be able to reconstruct them from the transition IDs.
    val path = checkerContext.trex.decodedExecution().path
    Trace(checkerContext.checkerInput.rootModule, path.map(_.assignments).toIndexedSeq,
        path.map(_ => SortedSet[String]()).toIndexedSeq, ())
  }

  /**
   * Produce a configuration from the parameters of the loadSpec method.
   * @param params
   *   specification parameters
   * @return
   *   the configuration for spawning a CheckerModule
   */
  private def createConfigFromParams(params: LoadSpecParams): Try[HasCheckerPreds] = {
    // pack the sources into the config
    val source = SourceOption.StringSource(params.sources.head, params.sources.tail)
    val input = config.get.input.copy(source = Some(source))
    val configWithInput = config.get.copy(input = input, output = config.get.output.copy(output = None))
    WithCheckerPreds(configWithInput)
      .map(cfg => {
        // We do not need to set the checker options, as we do not run the model checker.
        // We just prepare the context for the remote mode.
        // Most of the options are irrelevant, as the remote algorithm does its own exploration.
        cfg.copy(
            checker = cfg.checker.copy(
                algo = Remote,
                smtEncoding = OOPSLA19,
                // TODO: propagate the tuning options from LoadSpecParams
                tuning = immutable.Map[String, String](),
                discardDisabled = false,
                noDeadlocks = true,
                maxError = 1,
                // TODO: propagate from LoadSpecParams
                timeoutSmtSec = 0,
            ),
            // TODO: this is the minimal setup for doing anything useful
            predicates = cfg.predicates.copy(
                behaviorSpec = InitNextSpec(params.init, params.next),
                invariants = params.invariants,
            ),
        )
      })
  }
}

/**
 * A simple JSON-RPC servlet that handles requests for the exploration service.
 * @param service
 *   exploration service that processes the exploration logic
 */
@WebServlet(urlPatterns = Array("/rpc"), asyncSupported = true)
class JsonRpcServlet(service: ExplorationService) extends HttpServlet with LazyLogging {

  /** The number of threads to keep in the pool */
  val CORE_POOL_SIZE = 16

  /** The maximum number of threads to allow in the pool */
  val MAX_POOL_SIZE = 1024

  /**
   * When the number of threads is greater than the core, this is the maximum time that excess idle threads will wait
   * for new tasks before terminating.
   */
  val KEEP_ALIVE_SEC = 60L

  // Our own bounded pool, to avoid blocking Jetty threads
  private val executor = new ThreadPoolExecutor(
      CORE_POOL_SIZE,
      MAX_POOL_SIZE,
      KEEP_ALIVE_SEC,
      TimeUnit.SECONDS,
      new LinkedBlockingQueue[Runnable](MAX_POOL_SIZE),
      (r: Runnable) => {
        val t = new Thread(r, "rpc-compute-pool")
        t.setDaemon(true)
        t
      },
  )
  // data mapper for JSON serialization/deserialization
  // using Jackson with Scala module for better compatibility with case classes
  private val mapper = new ObjectMapper().registerModule(DefaultScalaModule)

  override def doPost(req: HttpServletRequest, resp: HttpServletResponse): Unit = {
    // Start async and disable its (30s default) timeout for truly long jobs:
    val async = req.startAsync
    async.setTimeout(0) // 0 = no timeout
    val runnable: Runnable = () => {
      try {
        val responseJson = processRequest(req)
        resp.setContentType("application/json")
        val writer = resp.getWriter
        mapper.writeValue(writer, responseJson)
        writer.flush()
      } catch {
        case ex: Exception =>
          logger.error("Failed to process the request", ex)
          resp.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR)
      } finally {
        async.complete()
      }
    }
    executor.submit(runnable)
  }

  private def processRequest(req: HttpServletRequest): ObjectNode = {
    val input = req.getInputStream
    val requestJson = mapper.readTree(input)

    val method = requestJson.path("method").asText()
    val paramsNode = requestJson.path("params")
    val id = requestJson.path("id")

    // Build JSON-RPC response
    val responseJson = mapper.createObjectNode()
    responseJson.put("jsonrpc", "2.0")
    responseJson.set("id", id)

    val errorOrResult: Either[ServiceError, ExplorationServiceResult] =
      try {
        // Dispatch methods manually
        method match {
          case "loadSpec" =>
            new JsonParameterParser(mapper)
              .parseLoadSpec(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.loadSpec(serviceParams))

          case "disposeSpec" =>
            new JsonParameterParser(mapper)
              .parseDisposeSpec(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.disposeSpec(serviceParams))

          case "assumeTransition" =>
            new JsonParameterParser(mapper)
              .parseAssumeTransition(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.assumeTransition(serviceParams))

          case "nextStep" =>
            new JsonParameterParser(mapper)
              .parseNextStep(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.nextStep(serviceParams))

          case "checkInvariant" =>
            new JsonParameterParser(mapper)
              .parseCheckInvariant(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.checkInvariant(serviceParams))

          case _ =>
            Left(ServiceError(JsonRpcCodes.METHOD_NOT_FOUND, s"Method not found: $method"))
        }
      } catch {
        case ex: Exception =>
          Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR, s"Internal error: ${ex.getMessage}"))
      }

    errorOrResult match {
      case Left(error) =>
        responseJson.set[JsonNode]("error", mapper.valueToTree[JsonNode](error))

      case Right(result) =>
        responseJson.set[JsonNode]("result", mapper.valueToTree[JsonNode](result))
    }

    responseJson
  }
}

object JsonRpcServerApp {
  def run(config: Try[ApalacheConfig], port: Int): Unit = {
    val server = new Server(port)
    val context = new ServletContextHandler(ServletContextHandler.SESSIONS)
    context.setContextPath("/")
    server.setHandler(context)

    val service = new ExplorationService(config)
    context.addServlet(new ServletHolder(new JsonRpcServlet(service)), "/rpc")

    server.start()
    println(s"JSON-RPC server running on http://localhost:$port/rpc")
    server.join()
  }

  def main(args: Array[String]): Unit = {
    val port = if (args.nonEmpty) args(0).toInt else 8822
    val cfg = ConfigManager("{common.command: 'server'}")
    run(cfg, port)
  }
}

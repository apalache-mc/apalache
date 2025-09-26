package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.Algorithm.Remote
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import at.forsyte.apalache.infra.passes.options.OptionGroup.{HasCheckerPreds, WithCheckerPreds}
import at.forsyte.apalache.infra.passes.options.SMTEncoding.OOPSLA19
import at.forsyte.apalache.infra.passes.options.{Config, SourceOption}
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import com.google.inject.Injector
import com.typesafe.scalalogging.LazyLogging
import jakarta.servlet.http.{HttpServlet, HttpServletRequest, HttpServletResponse}
import org.eclipse.jetty.server.Server
import org.eclipse.jetty.servlet.{ServletContextHandler, ServletHolder}

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.concurrent.TrieMap
import scala.collection.immutable
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
        nTraceInvariants = checkerInput.verificationConditions.traceInvariantsAndNegations.size,
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
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid transition ID: $transitionId must be non-negative"))
        } else {
          Right(checkerContext)
        }

      case None =>
        Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Session not found: $sessionId"))
    }

    // Prepare the transition. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map { checkerContext => {
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
            )
        )
      })
  }
}

/**
 * A simple JSON-RPC servlet that handles requests for the exploration service.
 * @param service
 *   exploration service that processes the exploration logic
 */
class JsonRpcServlet(service: ExplorationService) extends HttpServlet {
  // data mapper for JSON serialization/deserialization
  // using Jackson with Scala module for better compatibility with case classes
  private val mapper = new ObjectMapper().registerModule(DefaultScalaModule)

  override def doPost(req: HttpServletRequest, resp: HttpServletResponse): Unit = {
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

    resp.setContentType("application/json")
    mapper.writeValue(resp.getOutputStream, responseJson)
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

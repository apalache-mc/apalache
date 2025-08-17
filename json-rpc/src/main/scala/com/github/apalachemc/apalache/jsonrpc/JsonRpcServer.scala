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

import java.util.concurrent.locks.ReadWriteLock
import scala.collection.immutable
import scala.util.{Random, Try}

/**
 * All kinds of the results that the exploration service can return.
 */
sealed abstract class ExplorationServiceResult

/**
 * Parameters for preparing a symbolic transition in the solver context.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param transitionId
 *   the number of transition to prepare, starting from 0. On step 0, it must be in the range `[0, nInitTransitions)`,
 *   on step 1 and later, it must be in the range `[0, nNextTransitions)`.
 * @param checkEnabled
 *   whether to check if the transition is enabled. If `false`, the transition is prepared and assumed, but no
 *   satisfiability is checked
 * @param timeoutSec
 *   the timeout in seconds for checking satisfiability. If `0`, the default timeout is used. This parameter is ignored
 *   if `checkEnabled` is `false`.
 */
case class AssumeTransitionParams(
    sessionId: String,
    transitionId: Int,
    checkEnabled: Boolean,
    timeoutSec: Int)

object AssumeTransitionParams {
  def apply(sessionId: String, transitionId: Int): AssumeTransitionParams = {
    new AssumeTransitionParams(sessionId, transitionId, checkEnabled = true, timeoutSec = 0)
  }

  def apply(sessionId: String, transitionId: Int, checkEnabled: Boolean): AssumeTransitionParams = {
    new AssumeTransitionParams(sessionId, transitionId, checkEnabled, timeoutSec = 0)
  }
}

object TransitionStatus extends Enumeration {
  type TransitionStatus = Value
  val ENABLED, DISABLED, UNKNOWN = Value
}
import TransitionStatus.TransitionStatus

/**
 * The result of preparing a symbolic transition.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID for recovering the context after the transition has been assumed.
 * @param transitionId
 *   the number of the prepared transition
 * @param status
 *   status of the transition: "ENABLED", "DISABLED", or "UNKNOWN"
 */
case class AssumeTransitionResult(
    sessionId: String,
    snapshotId: Int,
    transitionId: Int,
    status: TransitionStatus)
    extends ExplorationServiceResult

/**
 * The result of loading a specification.
 * @param sessionId
 *   the new session ID
 * @param snapshotId
 *   the snapshot ID for recovering the context right after loading the specification.
 * @param specParameters
 *   the specification parameters that are needed for symbolic path exploration
 */
case class LoadSpecResult(sessionId: String, snapshotId: Int, specParameters: SpecParameters)
    extends ExplorationServiceResult

/**
 * Specification parameters that are needed for symbolic path exploration. These numbers may be different from what the
 * user expects by reading the specification, as transitions and invariants are decomposed.
 *
 * @param nInitTransitions
 *   the number of initial symbolic transitions
 * @param nNextTransitions
 *   the number of next symbolic transitions
 * @param nStateInvariants
 *   the number of state invariants
 * @param nActionInvariants
 *   the number of action invariants
 * @param nTraceInvariants
 *   the number of trace invariants
 * @param hasView
 *   whether a view predicate is present in the specification
 */
case class SpecParameters(
    nInitTransitions: Int,
    nNextTransitions: Int,
    nStateInvariants: Int,
    nActionInvariants: Int,
    nTraceInvariants: Int,
    hasView: Boolean)

/**
 * The result of disposing a specification.
 * @param sessionId
 *   the ID of the previously loaded specification
 */
case class DisposeSpecResult(sessionId: String) extends ExplorationServiceResult

/**
 * Parameters for switching to the next step in symbolic path exploration.
 * @param sessionId
 *   the ID of the previously loaded specification
 */
case class NextStepParams(sessionId: String)

/**
 * The result of switching to the next step in symbolic path exploration.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID for recovering the context right after loading the specification.
 * @param newStepNo
 *   the number of the new step
 */
case class NextStepResult(sessionId: String, snapshotId: Int, newStepNo: Int) extends ExplorationServiceResult

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
  // the rwLock to prevent concurrent
  private val rwLock: ReadWriteLock = new java.util.concurrent.locks.ReentrantReadWriteLock()
  // a pRNG to generate session IDs, we keep it constant to make the tests deterministic
  private val random = new Random(20250731)
  // Guice injector instantiated for each session. This injector contains objects that are
  // configured via CheckerModule. Instead of doing model checking, it just prepares
  // ModelCheckerContext in the `remote` mode.
  private var sessions: Map[String, Injector] = Map.empty

  /**
   * Loads a specification based on the provided parameters.
   * @param params
   *   parsed loading parameters
   * @return
   */
  def loadSpec(params: LoadSpecParams): Either[ServiceError, LoadSpecResult] = {
    rwLock.writeLock().lock()
    val sessionId = random.nextInt().toHexString
    rwLock.writeLock().unlock()
    logger.info(s"Session $sessionId: Loading specification with ${params.sources.length} sources.")
    val options = createConfigFromParams(params).get
    // call the parser
    val passChainExecutor = PassChainExecutor(new CheckerModule(options))
    passChainExecutor.run() match {
      case Left(failure) =>
        return Left(ServiceError(failure.exitCode, s"Failed to load specification: $failure"))
      case Right(_) =>
        // Successfully loaded the spec, we can access the module later
        rwLock.writeLock().lock()
        sessions = sessions + (sessionId -> passChainExecutor.injector)
        rwLock.writeLock().unlock()
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
    val snapshot = checkerContext.trex.snapshot()
    val snapshotId = snapshot.contextSnapshot.rewriterLevel

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
    rwLock.writeLock().lock()
    val result =
      sessions.get(params.sessionId) match {
        case Some(injector) =>
          // get the checker context from the injector
          injector.synchronized {
            val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
            checkerModule.modelCheckerContext.foreach(_.trex.dispose())
          }
          sessions -= params.sessionId
          logger.info(s"Session ${params.sessionId}: Disposed.")
          Right(DisposeSpecResult(params.sessionId))
        case None =>
          Left(ServiceError(-32602, s"Session not found: ${params.sessionId}"))
      }

    rwLock.writeLock().unlock()
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
    // validate the input parameters under the global lock
    rwLock.readLock().lock()
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        // prepare the transition
        val stepNo = checkerContext.trex.stepNo
        val transitions = if (stepNo == 0) {
          checkerContext.checkerInput.initTransitions
        } else {
          checkerContext.checkerInput.nextTransitions
        }
        if (transitionId < 0 || transitionId >= transitions.size) {
          Left(ServiceError(-32602, s"Invalid transition ID: $transitionId not in [0, ${transitions.size})"))
        } else {
          Right((checkerContext, transitions(transitionId)))
        }

      case None =>
        Left(ServiceError(-32602, s"Session not found: $sessionId"))
    }
    rwLock.readLock().unlock()

    // Prepare the transition. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map {
        case (checkerContext, actionExpr) => {
          checkerContext.synchronized {
            val stepNo = checkerContext.trex.stepNo
            val snapshotBefore = checkerContext.trex.snapshot()
            val snapshotBeforeId = snapshotBefore.contextSnapshot.rewriterLevel
            // Upload the transition into the SMT context.
            // It returns the result of a simple check that does not check satisfiability.
            val isEnabled = checkerContext.trex.prepareTransition(transitionId, actionExpr)
            if (!isEnabled) {
              checkerContext.trex.recover(snapshotBefore)
              logger.info(
                  s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: transition $transitionId DISABLED")
              AssumeTransitionResult(sessionId, snapshotBeforeId, transitionId, TransitionStatus.DISABLED)
            } else {
              // assume that this transition takes place
              checkerContext.trex.assumeTransition(transitionId)
              val snapshotAfter = checkerContext.trex.snapshot()
              val snapshotAfterId = snapshotAfter.contextSnapshot.rewriterLevel
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
                      checkerContext.trex.recover(snapshotBefore)
                    }
                    val status = if (isSat) TransitionStatus.ENABLED else TransitionStatus.DISABLED
                    logger.info(
                        s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId $status")
                    AssumeTransitionResult(sessionId, snapshotBeforeId, transitionId, status)
                  case None =>
                    // in case of timeout or unknown, we do not rollback the context, but return unknown
                    logger.info(
                        s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
                    AssumeTransitionResult(sessionId, snapshotAfter.contextSnapshot.rewriterLevel, transitionId,
                      TransitionStatus.UNKNOWN)
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
    rwLock.readLock().lock()
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        Right(checkerContext)

      case None =>
        Left(ServiceError(-32602, s"Session not found: $sessionId"))
    }
    rwLock.readLock().unlock()

    // Roll to the next step. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map { checkerContext =>
        {
          checkerContext.synchronized {
            val stepBeforeNo = checkerContext.trex.stepNo
            checkerContext.trex.nextState()
            val stepAfterNo = checkerContext.trex.stepNo
            val snapshot = checkerContext.trex.snapshot()
            val snapshotId = snapshot.contextSnapshot.rewriterLevel
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
              .fold(errorMessage => Left(ServiceError(-32602, errorMessage)),
                  serviceParams => service.loadSpec(serviceParams))

          case "disposeSpec" =>
            new JsonParameterParser(mapper)
              .parseDisposeSpec(paramsNode)
              .fold(errorMessage => Left(ServiceError(-32602, errorMessage)),
                  serviceParams => service.disposeSpec(serviceParams))

          case "assumeTransition" =>
            new JsonParameterParser(mapper)
              .parseAssumeTransition(paramsNode)
              .fold(errorMessage => Left(ServiceError(-32602, errorMessage)),
                  serviceParams => service.assumeTransition(serviceParams))

          case "nextStep" =>
            new JsonParameterParser(mapper)
              .parseNextStep(paramsNode)
              .fold(errorMessage => Left(ServiceError(-32602, errorMessage)),
                  serviceParams => service.nextStep(serviceParams))

          case _ =>
            Left(ServiceError(-32601, s"Method not found: $method"))
        }
      } catch {
        case ex: Exception =>
          Left(ServiceError(-32603, s"Internal error: ${ex.getMessage}"))
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

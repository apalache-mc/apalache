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
 * The result of loading a specification.
 * @param sessionId
 *   the new session ID
 * @param specParameters
 *   the specification parameters that are needed for symbolic path exploration
 */
case class LoadSpecResult(sessionId: String, specParameters: SpecParameters) extends ExplorationServiceResult

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
 *   the new session ID
 */
case class DisposeSpecResult(sessionId: String) extends ExplorationServiceResult

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
  // a pRNG to generate session IDs
  private val random = new Random(20250731)
  // Guice modules instantiated for each session.
  // We instantiate a CheckerModule for each session. Instead of doing model checking,
  // it just prepares ModelCheckerContext in the `remote` mode.
  private var sessions: Map[String, CheckerModule] = Map.empty

  /**
   * Loads a specification based on the provided parameters.
   * @param params
   *   parsed loading parameters
   * @return
   */
  def loadSpec(params: LoadSpecParams): Either[ServiceError, ExplorationServiceResult] = {
    rwLock.writeLock().lock()
    val sessionId = random.nextInt().toHexString
    rwLock.writeLock().unlock()
    logger.info(s"Session $sessionId: Loading specification with ${params.sources.length} sources.")
    val options = createConfigFromParams(params).get
    // call the parser
    val checker = new CheckerModule(options)
    val passChainExecutor = PassChainExecutor(checker)
    passChainExecutor.run() match {
      case Left(failure) =>
        return Left(ServiceError(failure.exitCode, s"Failed to load specification: $failure"))
      case Right(_) =>
        // Successfully loaded the spec, we can access the module later
        rwLock.writeLock().lock()
        sessions = sessions + (sessionId -> checker)
        rwLock.writeLock().unlock()
    }
    // get the singleton instance of BoundedModelCheckerPass from checker
    val checkerModule = passChainExecutor.injector.getInstance(classOf[BoundedCheckerPassImpl])
    val checkerInput = checkerModule.modelCheckerContext.get.checkerInput
    val specParameters = SpecParameters(
        nInitTransitions = checkerInput.initTransitions.size,
        nNextTransitions = checkerInput.nextTransitions.size,
        nStateInvariants = checkerInput.verificationConditions.stateInvariantsAndNegations.size,
        nActionInvariants = checkerInput.verificationConditions.actionInvariantsAndNegations.size,
        nTraceInvariants = checkerInput.verificationConditions.traceInvariantsAndNegations.size,
        hasView = checkerInput.verificationConditions.stateView.nonEmpty,
    )

    Right(LoadSpecResult(sessionId, specParameters))
  }

  /**
   * Dispose a previously loaded specification by its session ID.
   * @param params
   *   the parameters object that contains the session ID
   * @return
   */
  def disposeSpec(params: DisposeSpecParams): Either[ServiceError, ExplorationServiceResult] = {
    rwLock.writeLock().lock()
    val result =
      sessions.get(params.sessionId) match {
        case Some(_) =>
          sessions -= params.sessionId
          logger.info(s"Session ${params.sessionId} disposed successfully.")
          Right(DisposeSpecResult(params.sessionId))
        case None =>
          Left(ServiceError(-32602, s"Session not found: ${params.sessionId}"))
      }

    rwLock.writeLock().unlock()
    result
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
                // TODO: propagate the tuning options from params
                tuning = immutable.Map[String, String](),
                discardDisabled = false,
                noDeadlocks = true,
                maxError = 1,
                // TODO: propagate from params
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

package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import at.forsyte.apalache.infra.passes.options.{Config, OptionGroup, SourceOption}
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.tla.passes.imp.ParserModule
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import com.typesafe.scalalogging.LazyLogging
import jakarta.servlet.http.{HttpServlet, HttpServletRequest, HttpServletResponse}
import org.eclipse.jetty.server.Server
import org.eclipse.jetty.servlet.{ServletContextHandler, ServletHolder}

import scala.util.{Random, Try}

abstract class ExplorationServiceResult
case class LoadSpecResult(sessionId: String) extends ExplorationServiceResult

case class ServiceError(code: Int, message: String)

/**
 * A transition exploration service.
 */
class ExplorationService(config: Try[Config.ApalacheConfig]) extends LazyLogging {
  // a pRNG to generate session IDs
  private val random = new Random(20250731)
  // Guice modules instantiated for each session
  private var sessions: Map[String, ParserModule] = Map.empty

  /**
   * Loads a specification based on the provided parameters.
   * @param params
   *   parsed loading parameters
   * @return
   */
  def loadSpec(params: LoadSpecParams): Either[ServiceError, ExplorationServiceResult] = {
    val sessionId = random.nextInt().toHexString
    logger.info(s"Session $sessionId: Loading specification with ${params.sources.length} sources.")
    // pack the sources into the config
    val source = SourceOption.StringSource(params.sources.head, params.sources.tail)
    val input = config.get.input.copy(source = Some(source))
    val configWithInput = config.get.copy(input = input, output = config.get.output.copy(output = None))
    val options = OptionGroup.WithIO(configWithInput).get
    // call the parser
    val parser = new ParserModule(options)
    PassChainExecutor.run(parser) match {
      case Left(failure) =>
        return Left(ServiceError(failure.exitCode, s"Failed to load specification: $failure"))
      case Right(_) =>
        // Successfully loaded the spec, we can access the module later
        sessions = sessions + (sessionId -> parser)
    }
    Right(LoadSpecResult(sessionId))
  }
}

// JSON-RPC servlet
class JsonRpcServlet(service: ExplorationService) extends HttpServlet {
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
    println(s"JSON-RPC server running on http://localhost:${port}/rpc")
    server.join()
  }

  def main(args: Array[String]): Unit = {
    val port = if (args.nonEmpty) args(0).toInt else 8822
    val cfg = ConfigManager("{common.command: 'server'}")
    run(cfg, port)
  }
}

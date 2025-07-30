package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.module.scala.{DefaultScalaModule, ScalaObjectMapper}
import jakarta.servlet.http.{HttpServlet, HttpServletRequest, HttpServletResponse}
import org.eclipse.jetty.server.Server
import org.eclipse.jetty.servlet.{ServletContextHandler, ServletHolder}

import scala.util.Random

abstract class ExplorationServiceResult
case class LoadSpecResult(sessionId: String) extends ExplorationServiceResult

case class ServiceError(code: Int, message: String)

/**
 * A transition exploration service.
 */
class ExplorationService {
  private var sessions: Map[String, String] = Map.empty

  /**
   * Loads a specification based on the provided parameters.
   * @param params parsed loading parameters
   * @return
   */
  def loadSpec(params: LoadSpecParams): Either[ServiceError, ExplorationServiceResult] = {
    val sessionId = Random.nextInt().toHexString
    sessions = sessions + (sessionId -> params.sources.map(_._1).mkString(", "))
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
  def main(args: Array[String]): Unit = {
    val server = new Server(8080)
    val context = new ServletContextHandler(ServletContextHandler.SESSIONS)
    context.setContextPath("/")
    server.setHandler(context)

    val service = new ExplorationService()
    context.addServlet(new ServletHolder(new JsonRpcServlet(service)), "/rpc")

    server.start()
    println("JSON-RPC server running on http://localhost:8080/rpc")
    server.join()
  }
}

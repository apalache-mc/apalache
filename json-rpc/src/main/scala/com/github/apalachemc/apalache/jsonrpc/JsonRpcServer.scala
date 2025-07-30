package com.github.apalachemc.apalache.jsonrpc

import java.io.{BufferedReader, InputStreamReader, PrintWriter}
import java.net.ServerSocket

import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import jakarta.servlet.http.{HttpServlet, HttpServletRequest, HttpServletResponse}
import org.eclipse.jetty.server.Server
import org.eclipse.jetty.servlet.{ServletContextHandler, ServletHolder}

import scala.jdk.CollectionConverters._

// Simple service
class CalculatorService {
  def add(a: Int, b: Int): Int = a + b
}

// JSON-RPC servlet
class JsonRpcServlet(service: CalculatorService) extends HttpServlet {
  private val mapper = new ObjectMapper().registerModule(DefaultScalaModule)

  override def doPost(req: HttpServletRequest, resp: HttpServletResponse): Unit = {
    val input = req.getInputStream
    val requestJson = mapper.readTree(input)

    val jsonrpc = requestJson.path("jsonrpc").asText()
    val method = requestJson.path("method").asText()
    val paramsNode = requestJson.path("params")
    val id = requestJson.path("id")

    val (resultNode, errorNode) = try {
      // Dispatch methods manually
      val result: Any = method match {
        case "add" =>
          val params = paramsNode.elements().asScala.toSeq.map(_.asInt())
          service.add(params(0), params(1))
        case _ =>
          throw new RuntimeException(s"Method not found: $method")
      }

      (mapper.valueToTree[JsonNode](result), null)
    } catch {
      case ex: Exception =>
        val errorObj = mapper.createObjectNode()
        errorObj.put("code", -32601) // Method not found
        errorObj.put("message", ex.getMessage)
        (null, errorObj)
    }

    // Build JSON-RPC response
    val responseJson = mapper.createObjectNode()
    responseJson.put("jsonrpc", "2.0")
    responseJson.set("id", id)
    if (errorNode != null) {
      responseJson.set("error", errorNode)
    } else {
      responseJson.set("result", resultNode)
    }

    resp.setContentType("application/json")
    mapper.writeValue(resp.getOutputStream, responseJson)
  }
}


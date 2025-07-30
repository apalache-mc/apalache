package com.github.apalachemc.apalache.jsonrpc

import java.io.{BufferedReader, InputStreamReader, PrintWriter}
import java.net.ServerSocket

object JsonRpcServer {
  def main(args: Array[String]): Unit = {
    val port = 8080
    val server = new ServerSocket(port)
    println(s"JSON-RPC server running on port $port")
    while (true) {
      val client = server.accept()
      new Thread(() => handleClient(client)).start()
    }
  }

  def handleClient(socket: java.net.Socket): Unit = {
    val in = new BufferedReader(new InputStreamReader(socket.getInputStream))
    val out = new PrintWriter(socket.getOutputStream, true)
    try {
      val input = in.readLine()
      val response = handleRequest(input)
      out.println(response)
    } finally {
      in.close()
      out.close()
      socket.close()
    }
  }

  def handleRequest(request: String): String = {
    // Very basic JSON parsing for demonstration
    val parsed = JSON.parseFull(request)
    parsed match {
      case Some(map: Map[String, Any]) if map.get("method").contains("health") =>
        """{"jsonrpc":"2.0","result":"ok","id":1}"""
      case _ =>
        """{"jsonrpc":"2.0","error":{"code":-32601,"message":"Method not found"},"id":null}"""
    }
  }
}


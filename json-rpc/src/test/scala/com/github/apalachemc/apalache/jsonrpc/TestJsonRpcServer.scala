package com.github.apalachemc.apalache.jsonrpc

import org.eclipse.jetty.server.{NetworkConnector, Server}
import org.scalatest.funsuite.AnyFunSuite

class TestJsonRpcServer extends AnyFunSuite {
  test("server binds to IPv4 loopback by default") {
    val connector = networkConnector(JsonRpcServerApp.newServer(8822))

    assert(connector.getHost == "127.0.0.1")
  }

  test("server honors an explicit IP address") {
    val connector = networkConnector(JsonRpcServerApp.newServer("0.0.0.0", 8822))

    assert(connector.getHost == "0.0.0.0")
  }

  private def networkConnector(server: Server): NetworkConnector = {
    val connectors = server.getConnectors
    assert(connectors.length == 1)
    connectors.head.asInstanceOf[NetworkConnector]
  }
}

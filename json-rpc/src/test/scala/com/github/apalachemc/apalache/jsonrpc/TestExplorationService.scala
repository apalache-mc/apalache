package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.io.ConfigManager
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestExplorationService extends AnyFunSuite with BeforeAndAfter {
  private val text =
    """---- MODULE Inc ----
      |EXTENDS Integers
      |VARIABLE x
      |Init == x = 0
      |Next == x' = x + 1
      |=====================
      """.stripMargin

  private var service: ExplorationService = _

  before {
    val config = ConfigManager("{common.command: 'server'}")
    service = new ExplorationService(config)
  }

  test("load spec") {
    service.loadSpec(LoadSpecParams(sources = Seq(text))) match {
      case Right(LoadSpecResult(sessionId)) =>
        assert(sessionId.nonEmpty, "Session ID should not be empty")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("dispose spec") {
    service.loadSpec(LoadSpecParams(sources = Seq(text))) match {
      case Right(LoadSpecResult(sessionId)) =>
        service.disposeSpec(DisposeSpecParams(sessionId)) match {
          case Right(DisposeSpecResult(newSessionId)) =>
            assert(newSessionId == sessionId, "Session ID should remain the same after disposal")
          case Right(result) =>
            fail(s"Unexpected result: $result")
          case Left(error) =>
            fail(s"Failed to dispose specification: $error")
        }
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification for disposal: $error")
    }
  }
}

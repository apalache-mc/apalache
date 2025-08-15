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
      |VARIABLE
      |  \* @type: Int;
      |  x
      |Init == x = 0
      |Next == x' = x + 1 \/ x' = x - 1
      |=====================
      """.stripMargin

  private var service: ExplorationService = _

  before {
    val config = ConfigManager("{common.command: 'server'}")
    service = new ExplorationService(config)
  }

  test("load spec") {
    service.loadSpec(LoadSpecParams(sources = Seq(text))) match {
      case Right(LoadSpecResult(sessionId, params)) =>
        assert(sessionId.nonEmpty, "Session ID should not be empty")
        assert(params.nInitTransitions == 1, "Should have one initial transition")
        assert(params.nNextTransitions == 2, "Should have two next transitions")
        assert(params.nStateInvariants == 0, "Should have no state invariants")
        assert(params.nActionInvariants == 0, "Should have no action invariants")
        assert(params.nTraceInvariants == 0, "Should have no trace invariants")
        assert(!params.hasView, "Should have no view")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("dispose spec") {
    service.loadSpec(LoadSpecParams(sources = Seq(text))) match {
      case Right(LoadSpecResult(sessionId, _)) =>
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

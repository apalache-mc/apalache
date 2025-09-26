package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestJsonRequests extends AnyFunSuite {
  test("parse LoadSpecParams") {
    val text =
      """---- MODULE Inc ----
        |EXTENDS Integers
        |VARIABLE
        |  \* @type: Int;
        |  x
        |Init == x = 0
        |Next == x' = x + 1
        |=====================
      """.stripMargin
    // encode text in base64
    val encodedText = java.util.Base64.getEncoder.encodeToString(text.getBytes("UTF-8"))
    val input =
      s"""{"jsonrpc": "2.0", "method": "loadSpec", "params": { "sources": ["$encodedText"] }, "id": 1}"""
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseLoadSpec(inputJson.path("params"))
    parsed match {
      case Right(loadSpecParams: LoadSpecParams) =>
        assert(loadSpecParams.sources == Seq(text), "Session ID should not be empty")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse errors in LoadSpecParams") {
    val input = s"""{"jsonrpc": "2.0", "method": "loadSpec", "params": { "something": 42 }, "id": 1}"""
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseLoadSpec(inputJson.path("params"))
    parsed match {
      case Right(loadSpecParams: LoadSpecParams) =>
        fail("Expected failure, but got: " + loadSpecParams)
      case Left(_) =>
      // ok
    }
  }

  test("parse DisposeSpecParams") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "disposeSpec", "params": { "sessionId": "1a1555f8" }, "id": 1}"""
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseDisposeSpec(inputJson.path("params"))
    parsed match {
      case Right(params: DisposeSpecParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse errors DisposeSpecParams") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "disposeSpec", "params": { "sessionId": "" }, "id": 1}"""
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseDisposeSpec(inputJson.path("params"))
    if (parsed.isRight) {
      fail("Expected failure, but got: " + parsed)
    }
  }

  test("parse AssumeTransitionParams with missing optional snapshotId and timeoutSec") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "assumeTransition",
         |"params": { "sessionId": "1a1555f8", "transitionId": 1, "checkEnabled": true }, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseAssumeTransition(inputJson.path("params"))
    parsed match {
      case Right(params: AssumeTransitionParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.transitionId == 1, "Unexpected transition ID")
        assert(params.checkEnabled, "Expected checkEnabled to be true")
        assert(params.timeoutSec == 0, "Expected timeoutSec to be 0")
        assert(params.snapshotId == -1, "Expected default snapshotId to be -1")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse AssumeTransitionParams with all parameters") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "assumeTransition",
         |"params": { "sessionId": "1a1555f8", "snapshotId": 3, "transitionId": 1,
         |"checkEnabled": true, "timeoutSec": 600 }, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseAssumeTransition(inputJson.path("params"))
    parsed match {
      case Right(params: AssumeTransitionParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.transitionId == 1, "Unexpected transition ID")
        assert(params.checkEnabled, "Expected checkEnabled to be true")
        assert(params.timeoutSec == 600, "Expected timeoutSec to be 600")
        assert(params.snapshotId == 3, "Expected snapshotId to be 3")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse nextState") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "nextState", "params": { "sessionId": "1a1555f8" }, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseNextStep(inputJson.path("params"))
    parsed match {
      case Right(params: NextStepParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse CheckInvariantParams") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "checkInvariant",
         |"params": { "sessionId": "1a1555f8", "stateInvariantIds": [0,1], "actionInvariantIds": [2],
         |"traceInvariantIds": [3], "timeoutSec": 300 }, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseCheckInvariant(inputJson.path("params"))
    parsed match {
      case Right(params: CheckInvariantParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.stateInvariantIds == List(0, 1), "Unexpected stateInvariantIds")
        assert(params.actionInvariantIds == List(2), "Unexpected actionInvariantIds")
        assert(params.traceInvariantIds == List(3), "Unexpected traceInvariantIds")
        assert(params.timeoutSec == 300, "Expected timeoutSec to be 300")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }
}

package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestJsonRequests extends AnyFunSuite {
  val spec1: String =
    """---- MODULE Inc ----
      |EXTENDS Integers
      |VARIABLE
      |  \* @type: Int;
      |  x
      |Init == x = 0
      |Next == x' = x + 1
      |=====================
      """.stripMargin

  test("parse LoadSpecParams minimal") {
    // encode text in base64
    val encodedText = java.util.Base64.getEncoder.encodeToString(spec1.getBytes("UTF-8"))
    val input =
      s"""{"jsonrpc": "2.0", "method": "loadSpec", "params": { "sources": ["$encodedText"] }, "id": 1}"""
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseLoadSpec(inputJson.path("params"))
    parsed match {
      case Right(loadSpecParams: LoadSpecParams) =>
        assert(loadSpecParams.sources == Seq(spec1), "Session ID should not be empty")
        assert(loadSpecParams.init == "Init", "Unexpected init")
        assert(loadSpecParams.next == "Next", "Unexpected next")
        assert(loadSpecParams.invariants.isEmpty, "Invariants should be empty")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse LoadSpecParams with all parameters") {
    // encode text in base64
    val encodedText = java.util.Base64.getEncoder.encodeToString(spec1.getBytes("UTF-8"))
    val input =
      s"""{"jsonrpc": "2.0", "method": "loadSpec", "params": { "sources": ["$encodedText"],
         |"init": "MyInit", "next": "MyNext", "invariants": ["inv1", "inv2"],
         |"exports": ["MyView"]},"id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseLoadSpec(inputJson.path("params"))
    parsed match {
      case Right(loadSpecParams: LoadSpecParams) =>
        assert(loadSpecParams.sources == Seq(spec1), "Session ID should not be empty")
        assert(loadSpecParams.init == "MyInit", "Unexpected init")
        assert(loadSpecParams.next == "MyNext", "Unexpected next")
        assert(loadSpecParams.invariants == List("inv1", "inv2"), "Unexpected invariants")
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
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("parse AssumeTransitionParams with all parameters") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "assumeTransition",
         |"params": { "sessionId": "1a1555f8", "transitionId": 1,
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
      case Left(error) =>
        fail(s"Failed: $error")
    }
  }

  test("parse AssumeStateParams with all parameters") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "assumeState",
         |"params": { "sessionId": "1a1555f8",
         |"checkEnabled": true, "timeoutSec": 600,
         |"equalities": {"msg": "hello", "x": {"#bigint": "42"}}
         |}, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseAssumeState(inputJson.path("params"))
    parsed match {
      case Right(params: AssumeStateParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.checkEnabled, "Expected checkEnabled to be true")
        assert(params.timeoutSec == 600, "Expected timeoutSec to be 600")
        assert(params.equalities.size() == 2, "Expected 2 equalities")
        val msg = params.equalities.get("msg")
        assert(msg.isTextual && msg.asText() == "hello", "Unexpected value for msg")
        val x = params.equalities.get("x")
        assert(x.isObject && x.path("#bigint").asText() == "42", "Unexpected value for x")
      case Left(error) =>
        fail(s"Failed: $error")
    }
  }

  test("parse RollbackParams with all parameters") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "rollback",
         |"params": { "sessionId": "1a1555f8", "snapshotId": 3 }, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseRollback(inputJson.path("params"))
    parsed match {
      case Right(params: RollbackParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.snapshotId == 3, "Expected rollbackToSnapshotId to be 3")
      case Left(error) =>
        fail(s"Failed: $error")
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
        fail(s"Failed: $error")
    }
  }

  test("parse CheckInvariantParams") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "checkInvariant",
         |"params": { "sessionId": "1a1555f8", "invariantId": 3,
         |"timeoutSec": 300 }, "id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseCheckInvariant(inputJson.path("params"))
    parsed match {
      case Right(params: CheckInvariantParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.invariantId == 3, "Unexpected invariantId")
        assert(params.timeoutSec == 300, "Expected timeoutSec to be 300")
      case Left(error) =>
        fail(s"Failed: $error")
    }
  }

  test("parse QueryParams") {
    val input =
      s"""{"jsonrpc": "2.0", "method": "query",
         |"params": { "sessionId": "1a1555f8", "kinds": ["OPERATOR", "TRACE"], "operator": "View" },
         |"id": 1}""".stripMargin
    val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
    val inputJson = mapper.readTree(input)
    val parsed = new JsonParameterParser(mapper).parseQuery(inputJson.path("params"))
    parsed match {
      case Right(params: QueryParams) =>
        assert(params.sessionId == "1a1555f8", "Unexpected session ID")
        assert(params.kinds == List(QueryKind.OPERATOR, QueryKind.TRACE), "Unexpected kinds")
        assert(params.operator != "", "Expected `operator` to be defined")
      case Left(error) =>
        fail(s"Failed: $error")
    }
  }
}

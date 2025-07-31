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
        |VARIABLE x
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
}

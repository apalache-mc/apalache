package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.predef.TlaRealSet
import at.forsyte.apalache.tla.lir.{OperEx, SimpleFormalParam, TlaEx, TlaOperDecl, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestJsonWriter extends FunSuite with BeforeAndAfterEach {

  // compare expression and expected result (single-line formatting)
  def compare(ex: TlaEx, expected: String, indent: Int = -1): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new JsonWriter(printWriter, indent)
    writer.write(ex)
    printWriter.flush()
    assert(expected == stringWriter.toString)
  }

  // compare expression and expected result (multi-line formatting)
  def compareMultiLine(ex: TlaEx, expected: String): Unit =
    compare(ex, expected, 2)

  test("name") {
    compare(
      name("awesome"),
      """{"tla":"name","val":"awesome"}"""
    )
  }

  test("str") {
    compare(
      str("Hello, World!"),
      """"Hello, World!""""
    )
  }

  test("int") {
    compare(
      int(42),
      """{"tla":"int","val":"42"}"""
    )
  }

  test("RealSet") {
    compare(
      ValEx(TlaRealSet), // TODO: builders for sets? (Andrey)
      """{"tla":"set","val":"Real"}"""
    )
  }

  test("prime name") {
    compare(
      prime("awesome"),
      """{"tla":"prime","val":{"tla":"name","val":"awesome"}}"""
    )
  }

  test("empty set") {
    compare(
      enumSet(),
      """{"tla":"set","val":null}"""
    )
  }

  test("empty set multi-line") {
    compareMultiLine(
      enumSet(),
      """{
        |  "tla": "set",
        |  "val": null
        |}""".stripMargin
    )
  }

  test("singleton set") {
    compare(
      enumSet(42),
      """{"tla":"set","val":{"tla":"int","val":"42"}}"""
    )
  }

  test("enum set") {
    compare(
      enumSet(int(1), int(2), int(3)),
      """{"tla":"set","val":[{"tla":"int","val":"1"},{"tla":"int","val":"2"},{"tla":"int","val":"3"}]}"""
    )
  }

  test("enum set multi-line") {
    compareMultiLine(
      enumSet(int(1), int(2), int(3)),
      """{
        |  "tla": "set",
        |  "val": [
        |    {
        |      "tla": "int",
        |      "val": "1"
        |    },
        |    {
        |      "tla": "int",
        |      "val": "2"
        |    },
        |    {
        |      "tla": "int",
        |      "val": "3"
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("tuple") {
    compare(
      tuple(int(1), int(2), int(3)),
      """{"tla":"tuple","val":[{"tla":"int","val":"1"},{"tla":"int","val":"2"},{"tla":"int","val":"3"}]}"""
    )
  }
}


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
    assert(stringWriter.toString == expected)
  }

  // compare expression and expected result (multi-line formatting)
  def compareMultiLine(ex: TlaEx, expected: String): Unit =
    compare(ex, expected, 2)

  test("id") {
    compare(
      name("awesome"),
      """"awesome""""
    )
  }

  test("str") {
    compare(
      str("Hello, World!"),
      """{"str":"Hello, World!"}"""
    )
  }

  test("int") {
    compare(
      int(42),
      """{"int":"42"}"""
    )
  }

  test("RealSet") {
    compare(
      ValEx(TlaRealSet), // TODO: builders for sets? (Andrey)
      """{"set":"Real"}"""
    )
  }

  test("prime name") {
    compare(
      prime("awesome"),
      """{"prime":"awesome"}"""
    )
  }

  test("empty set") {
    compare(
      enumSet(),
      """{"enum":[]}"""
    )
  }
  //
  test("singleton set") {
    compare(
      enumSet(42),
      """{"enum":[{"int":"42"}]}"""
    )
  }

  test("singleton set multi-line") {
    compareMultiLine(
      enumSet(42),
      """{
        |  "enum": [
        |    {
        |      "int": "42"
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("enum") {
    compare(
      enumSet(int(1), int(2), int(3)),
      """{"enum":[{"int":"1"},{"int":"2"},{"int":"3"}]}"""
    )
  }

  test("enum multi-line") {
    compareMultiLine(
      enumSet(int(1), int(2), int(3)),
      """{
        |  "enum": [
        |    {
        |      "int": "1"
        |    },
        |    {
        |      "int": "2"
        |    },
        |    {
        |      "int": "3"
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("tuple") {
    compare(
      tuple(int(1), name("two"), str("three")),
      """{"tuple":[{"int":"1"},"two",{"str":"three"}]}"""
    )
  }

  test("conjunction") {
    compare(
      and(name("a"), name("b"), name("c")),
      """{"and":["a","b","c"]}"""
    )
  }

  test("minus") {
    compare(
      minus(int(1), int(2)),
      """{"-":[{"int":"1"},{"int":"2"}]}"""
    )
  }

  test("function definition") {
    compareMultiLine(
      funDef(plus("x", "y"), "x", "S", "y", "T"),
      """{
        |  "function": {
        |    "+": [
        |      "x",
        |      "y"
        |    ]
        |  },
        |  "where": [
        |    "x",
        |    "S",
        |    "y",
        |    "T"
        |  ]
        |}""".stripMargin
    )
  }

  test("function application") {
    // f[e]
    compare(
      appFun("f", "e"),
      """{"apply":"f","to":"e"}"""
    )
  }

  test("double function application") {
    // f[e][g]
    compare(
      appFun(appFun("f", "e"), "g"),
      """{"apply":{"apply":"f","to":"e"},"to":"g"}"""
    )
  }

  test("function except") {
    // [f EXCEPT ![k] = v]
    compare(
      except("f", "k", "v"),
      """{"except":"f","with":["k","v"]}"""
    )
  }

}

package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.predef.TlaRealSet
import at.forsyte.apalache.tla.lir.{OperEx, SimpleFormalParam, TlaEx, TlaOperDecl, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import scala.reflect.runtime.{universe => ru}

@RunWith(classOf[JUnitRunner])
class TestJsonWriter extends FunSuite with BeforeAndAfterEach {

  def getTypeTag[T: ru.TypeTag](obj: T) = ru.typeTag[T].tpe

  // compare expression and expected result (single-line formatting)
  def compare(ex: TlaEx, expected: String, indent: Int = -1): Unit = {
    ex match {
      case OperEx(op@_, args@_*) =>
        println(op.getClass)
      case _ => println("_")
    }
   // val theType = getTypeTag(ex).
   // println(ex.oper.toString)

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

  test("name") {
    compare(
      name("awesome"),
      """{"tla":"name","arg":"awesome"}"""
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
      """{"tla":"int","arg":"42"}"""
    )
  }

  test("RealSet") {
    compare(
      ValEx(TlaRealSet), // TODO: builders for sets? (Andrey)
      """{"tla":"set","arg":"Real"}"""
    )
  }

  test("prime name") {
    compare(
      prime("awesome"),
      """{"tla":"prime","arg":{"tla":"name","arg":"awesome"}}"""
    )
  }

//  test("empty set") {
//    compare(
//      enumSet(),
//      """{"tla":"enum","args":[]}"""
//    )
//  }
//
//  test("singleton set") {
//    compare(
//      enumSet(42),
//      """{"tla":"set","val":[{"tla":"int","val":"42"}]}"""
//    )
//  }
//
//  test("singleton set multi-line") {
//    compareMultiLine(
//      enumSet(42),
//      """{
//        |  "tla": "set",
//        |  "val": [
//        |    {
//        |      "tla": "int",
//        |      "val": "42"
//        |    }
//        |  ]
//        |}""".stripMargin
//    )
//  }
//
//  test("enum set") {
//    compare(
//      enumSet(int(1), int(2), int(3)),
//      """{"tla":"set","val":[{"tla":"int","val":"1"},{"tla":"int","val":"2"},{"tla":"int","val":"3"}]}"""
//    )
//  }
//
//  test("enum set multi-line") {
//    compareMultiLine(
//      enumSet(int(1), int(2), int(3)),
//      """{
//        |  "tla": "set",
//        |  "val": [
//        |    {
//        |      "tla": "int",
//        |      "val": "1"
//        |    },
//        |    {
//        |      "tla": "int",
//        |      "val": "2"
//        |    },
//        |    {
//        |      "tla": "int",
//        |      "val": "3"
//        |    }
//        |  ]
//        |}""".stripMargin
//    )
//  }
//
//  test("minus") {
//    compare(
//      minus(int(1), int(2)),
//      """{"tla":"--","val":[{"tla":"int","val":"1"},{"tla":"int","val":"2"}]}"""
//    )
//  }
}


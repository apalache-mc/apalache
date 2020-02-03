package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{OperEx, SimpleFormalParam, TlaEx, TlaOperDecl}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestJsonWriter extends FunSuite with BeforeAndAfterEach {
  private var stringWriter = new StringWriter()
  private var printWriter = new PrintWriter(stringWriter)
  private var writer = new JsonWriter(printWriter)

  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
    writer = new JsonWriter(printWriter)
  }

  protected def compare(ex: TlaEx, expected: String): Unit = {
    writer.write(ex)
    printWriter.flush()
    assert(expected == stringWriter.toString)
  }

  test("name") {
    compare(
      name("awesome"),
      """{"kind":"name","value":"awesome"}"""
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
      """{"kind":"int","value":"42"}"""
    )
  }
}


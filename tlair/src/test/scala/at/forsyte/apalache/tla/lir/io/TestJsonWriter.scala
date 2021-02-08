package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.UntypedPredefs._

class TestJsonWriter extends TestJson {

  def compareModule(mod: TlaModule, json: String, indent: Int = -1): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new JsonWriter(printWriter, indent)
    writer.write(mod)
    printWriter.flush()
    assert(stringWriter.toString == json)
  }

  def compare(ex: TlaEx, expected: String, indent: Int = -1): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new JsonWriter(printWriter, indent)
    writer.write(ex)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }
}

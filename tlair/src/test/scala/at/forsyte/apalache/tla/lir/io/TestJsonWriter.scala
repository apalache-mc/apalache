package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}
import at.forsyte.apalache.tla.lir._

class TestJsonWriter extends TestJson {

  def compare(ex: TlaEx, expected: String, indent: Int = -1): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new JsonWriter(printWriter, indent)
    writer.write(ex)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }
}

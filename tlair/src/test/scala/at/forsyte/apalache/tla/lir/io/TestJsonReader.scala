package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir._

class TestJsonReader extends TestJson {

  // check that after reading from json the result matches expected
  def compare(expected: TlaEx, json: String, indent: Int = -1): Unit = {
    assert(JsonReader.read(json) == expected)
  }
}

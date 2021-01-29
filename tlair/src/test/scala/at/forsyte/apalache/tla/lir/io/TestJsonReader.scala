package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir._

class TestJsonReader extends TestJson {

  def compareModule(expected: TlaModule, json: String, indent: Int = -1): Unit = {
    val mod = JsonReader.readModule(json)
    assert(mod.name == expected.name)
    assert(mod.declarations == expected.declarations)
  }

  def compare(expected: TlaEx, json: String, indent: Int = -1): Unit = {
    assert(JsonReader.readExpr(json) == expected)
  }
}

package at.forsyte.apalache.infra.passes.options

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestOptions extends AnyFunSuite {
  test("Can construct SourceOption.FileSource for ITF files") {
    import SourceOption._
    assert(FileSource(new java.io.File("foo.itf.json")).format == Format.Itf)
  }

  test("Non-ITF JSON files are not recognized as ITF format") {
    import SourceOption._

    assert(FileSource(new java.io.File("foo.json")).format == Format.Json)
  }
}

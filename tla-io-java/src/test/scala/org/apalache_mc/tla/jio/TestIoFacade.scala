package org.apalache_mc.tla.jio

import at.forsyte.apalache.io.annotations.PrettyWriterWithAnnotations
import at.forsyte.apalache.io.annotations.store.createAnnotationStore
import at.forsyte.apalache.io.lir.{PrettyWriter, TextLayout, TlaDeclAnnotator, TlaWriter}
import at.forsyte.apalache.tla.lir._
import org.apalache_mc.tla.jir._
import org.scalatest.funsuite.AnyFunSuite

import java.io.{PrintWriter, StringWriter}

class TestIoFacade extends AnyFunSuite {
  test("printing matches upstream layout, annotations and standard modules") {
    val b = new TlaTypedScopeUncheckedBuilder()
    val ex = b.plus(b.integer(1), b.integer(2))
    val module = TlaModule("M", Seq(b.decl("Value", ex)))
    val output = new StringWriter
    val writer = new PrintWriter(output)
    new PrettyWriterWithAnnotations(createAnnotationStore(), writer, TextLayout(100, 3))
      .write(module, TlaWriter.STANDARD_MODULES)
    writer.flush()
    val text = new TlaText(100, 3)
    assert(text.render((writer: PrintWriter) => text.writeWithStandard(module, writer)) == output.toString)
    output.getBuffer.setLength(0)
    new PrettyWriter(writer, TextLayout(100, 3), new TlaDeclAnnotator).write(ex)
    writer.flush()
    assert(text.render((writer: PrintWriter) => text.write(ex, writer)) == output.toString)
    intercept[IllegalArgumentException](new TlaText(0, 2))
    intercept[IllegalArgumentException](TlaJson.writeModule(module, -2))
    intercept[UnsupportedOperationException](TlaText.standardModules().clear())
  }
  test("single-module reader rejects a multi-module root") {
    val b = new TlaTypedScopeUncheckedBuilder()
    val json = ujson.read(TlaJson.writeModule(TlaModules.create("M", java.util.List.of(b.decl("X", b.bool(true)))), 2))
    val modules = json("modules").arr
    modules += modules.head
    intercept[TlaJsonException](TlaJson.readModule(json.render()))
  }
}

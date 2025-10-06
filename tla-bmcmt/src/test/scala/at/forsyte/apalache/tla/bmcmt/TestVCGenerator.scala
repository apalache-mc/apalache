package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.tla._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestVCGenerator extends AnyFunSuite {
  private val parser = DefaultType1Parser

  private def mkVCGen(): VCGenerator = {
    new VCGenerator(new IdleTracker)
  }

  test("simple invariant") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x > 0
        |====================
      """.stripMargin

    val mod = loadFromText("inv", text)
    val newMod = mkVCGen().genInv(mod, "Inv")
    assertDecl(newMod, "VCInv$0", "x > 0")
    assertDecl(newMod, "VCNotInv$0", "¬(x > 0)")
  }

  test("action invariant") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x' > x
        |====================
      """.stripMargin

    val mod = loadFromText("inv", text)
    val newMod = mkVCGen().genInv(mod, "Inv")
    assertDecl(newMod, "VCActionInv$0", "x' > x")
    assertDecl(newMod, "VCNotActionInv$0", "¬(x' > x)")
  }

  test("trace invariant") {
    // as trace VCGenerator checks the type of a trace invariant, we construct the declaration manually
    // hist[Len(hist)].x > hist[1].x
    val seqT = parser("Seq({ x: Int })")
    val hist = name("hist", seqT)
    val invBody = gt(app(app(hist, len(hist)), str("x")), app(app(hist, int(1)), str("x")))
    val traceInv = decl("TraceInv", invBody, param("hist", seqT))
    val xDecl = TlaVarDecl("x")(Typed(IntT1))
    val module = TlaModule("mod", Seq(xDecl, traceInv))

    val newMod = mkVCGen().genInv(module, "TraceInv")
    assertDecl(newMod, "VCTraceInv$0", """hist[Len(hist)]["x"] > hist[1]["x"]""")
    assertDecl(newMod, "VCNotTraceInv$0", """¬(hist[Len(hist)]["x"] > hist[1]["x"])""")
  }

  test("state view") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x' > x
        |View1 == x
        |====================
      """.stripMargin

    val mod = loadFromText("inv", text)
    val vcgen = mkVCGen()
    val newMod = vcgen.genView(vcgen.genInv(mod, "Inv"), "View1")
    assertDecl(newMod, "VCView$0", "x")
  }

  test("conjunctive invariant") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x > 0 /\ x < 10
        |====================
      """.stripMargin

    val mod = loadFromText("inv", text)
    val newMod = mkVCGen().genInv(mod, "Inv")
    assertDecl(newMod, "VCInv$0", "x > 0")
    assertDecl(newMod, "VCInv$1", "x < 10")
    assertDecl(newMod, "VCNotInv$0", "¬(x > 0)")
    assertDecl(newMod, "VCNotInv$1", "¬(x < 10)")
  }

  test("conjunction under label") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == L0 :: (x > 0 /\ x < 10)
        |====================
      """.stripMargin

    val mod = loadFromText("inv", text)
    val newMod = mkVCGen().genInv(mod, "Inv")
    assertDecl(newMod, "VCInv$0", "L0:: x > 0")
    assertDecl(newMod, "VCInv$1", "L0:: x < 10")
    assertDecl(newMod, "VCNotInv$0", "¬(L0:: x > 0)")
    assertDecl(newMod, "VCNotInv$1", "¬(L0:: x < 10)")
  }

  test("conjunction under universals") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x, S
        |Inv == \A z \in S: \A y \in S: y > 0 /\ y < 10
        |====================
      """.stripMargin

    val mod = loadFromText("inv", text)
    val newMod = mkVCGen().genInv(mod, "Inv")
    assertDecl(newMod, "VCInv$0", """∀z ∈ S: (∀y ∈ S: (y > 0))""")
    assertDecl(newMod, "VCInv$1", """∀z ∈ S: (∀y ∈ S: (y < 10))""")
    assertDecl(newMod, "VCNotInv$0", """¬(∀z ∈ S: (∀y ∈ S: (y > 0)))""")
    assertDecl(newMod, "VCNotInv$1", """¬(∀z ∈ S: (∀y ∈ S: (y < 10)))""")
  }

  private def assertDecl(mod: TlaModule, name: String, expectedBodyText: String): Unit = {
    val vc = mod.declarations.find(_.name == name)
    assert(vc.nonEmpty, s"(VC $name not found)")
    assert(vc.get.isInstanceOf[TlaOperDecl])
    assert(vc.get.asInstanceOf[TlaOperDecl].body.toString == expectedBodyText)
  }

  private def loadFromText(moduleName: String, text: String): TlaModule = {
    val locationStore = new SourceStore
    val (_, modules) =
      new SanyImporter(locationStore, createAnnotationStore()).loadFromSource(Source.fromString(text))
    modules(moduleName)
  }
}

package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.{findBodyOf, SanyImporter}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
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
    assertDecl(newMod, "VCInv$0", "L0∷ x > 0")
    assertDecl(newMod, "VCInv$1", "L0∷ x < 10")
    assertDecl(newMod, "VCNotInv$0", "¬(L0∷ x > 0)")
    assertDecl(newMod, "VCNotInv$1", "¬(L0∷ x < 10)")
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

  test("invariant that is a conjunct of init") {
    // the way one checks an inductive invariant: --init=IndInit --inv=IndInv
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |IndInv == x > 0 /\ x < 10
        |IndInit == x \in Int /\ (x > 0 /\ x < 10)
        |====================
      """.stripMargin

    assert(Seq(0, 1) == findImpliedByInit(text, "IndInit", "IndInv"))
  }

  test("invariant that is only partially a conjunct of init") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |IndInv == x > 0 /\ x < 10
        |IndInit == x \in Int /\ x < 10
        |====================
      """.stripMargin

    assert(Seq(1) == findImpliedByInit(text, "IndInit", "IndInv"))
  }

  test("invariant that is unrelated to init") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x > 0
        |Init == x = 3
        |====================
      """.stripMargin

    assert(findImpliedByInit(text, "Init", "Inv").isEmpty)
  }

  test("invariant under a disjunction in init") {
    // Init does not decompose into conjuncts, so nothing follows from it syntactically
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x > 0
        |Init == x > 0 \/ x < 0
        |====================
      """.stripMargin

    assert(findImpliedByInit(text, "Init", "Inv").isEmpty)
  }

  test("invariant that is a conjunct of init, up to the renaming of bound variables") {
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |IndInv == \A i \in 1..3: x > 0
        |IndInit == x \in Int /\ (\A i \in 1..3: x > 0)
        |====================
      """.stripMargin

    val renamed = new IncrementalRenaming(new IdleTracker).renameInModule(loadFromText("inv", text))
    // make sure that unique renaming has given the bound variables of the two copies different names
    val invBody = findBodyOf("IndInv", renamed.declarations: _*)
    val initConjuncts = findBodyOf("IndInit", renamed.declarations: _*).asInstanceOf[OperEx].args
    assert(initConjuncts.forall(_ != invBody))

    assert(Seq(0) == findImpliedByInit(renamed, "IndInit", "IndInv"))
  }

  test("action invariant that is a conjunct of init") {
    // an action invariant is never checked in the initial states
    val text =
      """---- MODULE inv ----
        |EXTENDS Integers
        |VARIABLE x
        |Inv == x' > 0
        |Init == x \in Int /\ x' > 0
        |====================
      """.stripMargin

    assert(findImpliedByInit(text, "Init", "Inv").isEmpty)
  }

  private def findImpliedByInit(moduleText: String, initName: String, invName: String): Seq[Int] =
    findImpliedByInit(loadFromText("inv", moduleText), initName, invName)

  private def findImpliedByInit(mod: TlaModule, initName: String, invName: String): Seq[Int] = {
    val vcgen = mkVCGen()
    vcgen.findInvariantsImpliedByInit(vcgen.genInv(mod, invName), initName)
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

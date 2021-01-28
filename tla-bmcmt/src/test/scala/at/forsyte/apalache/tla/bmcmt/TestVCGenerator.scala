package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{TlaModule, TlaOperDecl}
import at.forsyte.apalache.io.annotations.store._

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestVCGenerator extends FunSuite {
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
    val newMod = mkVCGen().gen(mod, "Inv")
    assertDecl(newMod, "VCInv$0", "x > 0")
    assertDecl(newMod, "VCNotInv$0", "¬(x > 0)")
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
    val newMod = mkVCGen().gen(mod, "Inv")
    assertDecl(newMod, "VCInv$0", "x > 0")
    assertDecl(newMod, "VCInv$1", "x < 10")
    assertDecl(newMod, "VCNotInv$0", "¬(x > 0)")
    assertDecl(newMod, "VCNotInv$1", "¬(x < 10)")
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
    val newMod = mkVCGen().gen(mod, "Inv")
    assertDecl(newMod, "VCInv$0", """∀z ∈ S: (∀y ∈ S: (y > 0))""")
    assertDecl(newMod, "VCInv$1", """∀z ∈ S: (∀y ∈ S: (y < 10))""")
    assertDecl(newMod, "VCNotInv$0", """¬(∀z ∈ S: (∀y ∈ S: (y > 0)))""")
    assertDecl(newMod, "VCNotInv$1", """¬(∀z ∈ S: (∀y ∈ S: (y < 10)))""")
  }

  private def assertDecl(
      mod: TlaModule, name: String, expectedBodyText: String
  ): Unit = {
    val vc = mod.declarations.find(_.name == name)
    assert(vc.nonEmpty, s"(VC $name not found)")
    assert(vc.get.isInstanceOf[TlaOperDecl])
    assert(vc.get.asInstanceOf[TlaOperDecl].body.toString == expectedBodyText)
  }

  private def loadFromText(moduleName: String, text: String): TlaModule = {
    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(locationStore, createAnnotationStore())
      .loadFromSource(moduleName, Source.fromString(text))
    modules(moduleName)
  }
}

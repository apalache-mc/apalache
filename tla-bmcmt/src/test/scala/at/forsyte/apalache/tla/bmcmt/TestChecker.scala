package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.lir.{TlaModule, TlaOperDecl}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestChecker extends FunSuite {
  test("check Boolean constants") {
    // prepare the input
    val text =
      """---- MODULE boolconst ----
        |Init == FALSE
        |Next == TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("boolconst", Source.fromString(text))
    val mod = expectSingleModule("boolconst", rootName, modules)
    val init = expectOperatorDeclaration("Init", 0, mod)
    val next = expectOperatorDeclaration("Next", 1, mod)
    // initialize the model checker
    val checker = new Checker(mod, init, next)
    // check for 10 steps
    val outcome = checker.check(10)
    assert(Checker.Outcome.Deadlock == outcome)
  }

  ////////////////////////////////////////////////////////////////////
  private def expectOperatorDeclaration(expectedName: String, idx: Int, mod: TlaModule): TlaOperDecl = {
    mod.declarations(idx) match {
      case decl: TlaOperDecl =>
        assert(expectedName == decl.name)
        decl

      case _ =>
        fail("Expected operator " + expectedName + " at position " + idx)
    }
  }

  // copied from TestSanyImporter
  private def expectSingleModule(expectedRootName: String, rootName: String, modules: Map[String, TlaModule]): TlaModule = {
    assert(expectedRootName == rootName)
    assert(1 == modules.size)
    val root = modules.get(rootName)
    root match {
      case Some(mod) =>
        mod

      case None =>
        fail("Module " + rootName + " not found")
    }
  }

}

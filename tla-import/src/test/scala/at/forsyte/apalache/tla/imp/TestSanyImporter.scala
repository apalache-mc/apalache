package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaDecimal, TlaInt, TlaStr}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

/**
  * Tests for the SANY importer.
  *
  * @author konnov
  */
@RunWith(classOf[JUnitRunner])
class TestSanyImporter extends FunSuite {
  test("empty module") {
    val text =
      """---- MODULE justASimpleTest ----
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("justASimpleTest", Source.fromString(text))
    assert("justASimpleTest" == rootName)
  }

  test("one variable") {
    val text =
      """---- MODULE onevar ----
        |VARIABLE x
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("onevar", Source.fromString(text))
    val mod = expectModule("onevar", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case vd: TlaVarDecl =>
        assert("x" == vd.name)

      case _ =>
        fail("Expected a declaration of variable x")
    }
  }

  test("one constant") {
    val text =
      """---- MODULE oneconst ----
        |CONSTANT n
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("oneconst", Source.fromString(text))
    val mod = expectModule("oneconst", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case constDecl: TlaConstDecl =>
        assert("n" == constDecl.name)
    }
  }

  test("constant operator (int)") {
    val text =
      """---- MODULE constop ----
        |MyOp == 1
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaInt(1)) == actionDecl.body)
    }
  }

  test("constant operator (decimal)") {
    val text =
      """---- MODULE constop ----
        |MyOp == 123.456
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaDecimal(BigDecimal("123.456"))) == actionDecl.body)
    }
  }

  test("constant operator (string)") {
    val text =
      """---- MODULE constop ----
        |MyOp == "Hello"
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaStr("Hello")) == actionDecl.body)
    }
  }

  test("constant operator (FALSE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == FALSE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(false)) == actionDecl.body)
    }
  }

  test("constant operator (TRUE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(true)) == actionDecl.body)
    }
  }

  ////////////////////////////////////////////////////////////////////
  private def expectModule(expectedRootName: String, rootName: String, modules: Map[String, TlaModule]): TlaModule = {
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

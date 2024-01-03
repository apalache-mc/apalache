package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, OperParam, TlaEx, TlaOperDecl, ValEx}
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaIntSet}
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

import scala.io.Source

/**
 * A collection of tests that check how SanyImporter processes instances.
 *
 * @author
 *   Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestSanyImporterInstances extends SanyImporterTestBase {

  test("instances") {
    val text =
      """---- MODULE inst ----
        |---- MODULE A ----
        |EXTENDS Naturals
        |CONSTANT N
        |F(x) == x + N
        |G == F(3)
        |================================
        |CONSTANT M
        |J == INSTANCE A WITH N <- M
        |\* I(V, K) == INSTANCE A WITH N <- K
        |---- MODULE B ----
        |---- MODULE C ----
        |H(x) == x
        |================================
        |CONSTANT M
        |C2 == INSTANCE C
        |F(x) == C2!H(x)
        |================================
        |B2 == INSTANCE B
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(2 == modules.size) // inst + Naturals
    // the root module and A
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find {
      _.name == "J!F"
    } match {
      case Some(
              TlaOperDecl(
                  _,
                  params,
                  OperEx(TlaArithOper.plus, NameEx("x"), NameEx("M")),
              )
          ) =>
        assert(params.length == 1)
        assert(params.head.isInstanceOf[OperParam])
        assert("x" == params.head.name)

      case e =>
        fail("expected the body for J!F, found: " + e)
    }
    val fDecl = root.declarations.find {
      _.name == "J!F"
    }.get
    root.declarations.find {
      _.name == "J!G"
    } match {
      case Some(TlaOperDecl(_, params, body)) =>
        assert(params.isEmpty)
        val expected: TlaEx = appDecl(fDecl.asInstanceOf[TlaOperDecl], int(3))
        assert(body == expected)

      case _ =>
        fail("expected the body for J!G")
    }
    // an instance with parameters, not working yet
    /*
    root.declarations.find { _.name == "I!F" } match {
      case Some(TlaOperDecl(_, params,
          OperEx(TlaArithOper.plus, NameEx("x"), NameEx("K")))) =>
        assert(params.length == 3)
        assert(params.head == FormalParam("V"))
        assert(params(1) == FormalParam("K"))
        assert(params(2) == FormalParam("x"))

      case _ =>
        fail("expected the body for I!F")
    }
     */
    // two instances
    root.declarations.find {
      _.name == "B2!C2!H"
    } match {
      case Some(TlaOperDecl(_, params, NameEx("x"))) =>
        assert(params.length == 1)
        assert(params.head == OperParam("x"))

      case _ =>
        fail("expected the body for B2!C2!H")
    }
  }

  test("lookup order in INSTANCE") {
    // regression: SanyImporter was resolving the names in the wrong order
    val text =
      """---- MODULE imports ----
        |---- MODULE M ----
        |a == {}
        |b == a
        |================================
        |a(self) == {self}
        |I == INSTANCE M
        |c == a(1)
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(4 == root.declarations.size)
    val aOfM = root.declarations.head
    // check that the root module has indeed the definition a(self) == {self}, not a == {}
    assert(
        aOfM.isInstanceOf[TlaOperDecl] && aOfM
          .asInstanceOf[TlaOperDecl]
          .formalParams
          .size == 1
    )
  }

  test("substitution in INSTANCE") {
    // regression: the importer was not able to substitute a variable with an operator, e.g., in Paxos
    val text =
      """---- MODULE Paxos ----
        |---- MODULE Consensus ----
        |VARIABLE chosen
        |C == chosen
        |================================
        |---- MODULE Voting ----
        |chosen == 1
        |C == INSTANCE Consensus
        |================================
        |V == INSTANCE Voting
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    expectSourceInfoInDefs(modules(rootName))
  }

  test("LOCAL operator inside INSTANCE") {
    val text =
      """---- MODULE localInInstance ----
        |---- MODULE M ----
        |LOCAL a == {}
        |b == a
        |================================
        |I == INSTANCE M
        |c == I!b
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(2 == root.declarations.size)
    val bOfM = root.declarations.head
    // as "a" is LOCAL, it does not appear in the declarations, but it becomes a LET-IN definition inside b
    assert("I!b" == bOfM.name)
    // BUGFIX #576: use a unique lookup prefix to guarantee name uniqueness
    bOfM match {
      case TlaOperDecl(name, List(), LetInEx(OperEx(TlaOper.apply, NameEx(appliedName)), localDef)) =>
        assert("I!b" == name)
        assert(appliedName.startsWith("LOCAL"))
        assert(appliedName.endsWith("!I!a"))
        localDef match {
          case TlaOperDecl(localName, List(), body) =>
            assert(appliedName == localName)
            assert(OperEx(TlaSetOper.enumSet) == body)

          case _ =>
            fail("Expected an operator definition " + appliedName)
        }

      case _ => fail("Unexpected operator structure")
    }
  }

  // regression for #112
  test("LET-IN inside INSTANCE") {
    val text =
      """---- MODULE letInInstance ----
        |---- MODULE M ----
        |VARIABLE x
        |a ==
        |  LET b == {} IN
        |  b
        |================================
        |VARIABLE x
        |INSTANCE M
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(2 == root.declarations.size)
    val aOfM = root.declarations(1)
    aOfM.asInstanceOf[TlaOperDecl].body match {
      case LetInEx(body, bDecl) =>
        assert(sourceStore.contains(body.ID))
        assert(sourceStore.contains(bDecl.body.ID))

      case _ =>
        fail("expected declaration of b")
    }
  }

  // regression for #143
  test("Lookup inside substitutions") {
    val text =
      """------------------- MODULE P ----------------------
        |------------------- MODULE Vot ----------------------
        |------------------- MODULE Cons -------------------
        |VARIABLE chosen
        |Init == chosen = {}
        |Next == chosen = {2}
        |===================================================
        |chosen == {2}
        |C == INSTANCE Cons
        |===================================================
        |V == INSTANCE Vot
        |===================================================""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // expect V!chosen, V!C!Init and V!C!Next
    assert(3 == root.declarations.size)
    val next = root.declarations
      .find(_.name == "V!C!Next")
      .getOrElse(fail("V!C!Next not found"))
    assert("V!C!Next" == next.name)
    next.asInstanceOf[TlaOperDecl].body match {
      case body @ OperEx(
              TlaOper.eq,
              OperEx(TlaOper.apply, NameEx("V!chosen")),
              OperEx(TlaSetOper.enumSet, ValEx(TlaInt(i))),
          ) =>
        assert(i == 2)
        assert(sourceStore.contains(body.ID))

      case _ =>
        fail("expected V!C!Next == V!chosen = {2}")
    }
  }

  // regression for #1254
  test("renaming higher-order operators inside instances") {
    val text =
      """---- MODULE test1254 ----
        |---- MODULE base ----
        |FF(a) == TRUE
        |Check(a, func(_)) == func(a)
        |B == Check(1, FF)
        |==============================
        |BASE == INSTANCE base
        |==============================""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    val root = modules(rootName)
    val base = root.declarations
      .find(_.name == "BASE!B")
      .getOrElse(fail("BASE!B"))
    base.asInstanceOf[TlaOperDecl].body match {
      case OperEx(TlaOper.apply, NameEx("BASE!Check"), args @ _*) =>
        assert(ValEx(TlaInt(1)) == args.head)
        assert(NameEx("BASE!FF") == args(1))

      case _ =>
        fail("unexpected structure")
    }
  }

  // regression for #143
  test("Series of substitutions") {
    val text =
      """------------------- MODULE A ----------------------
        |------------------- MODULE B ----------------------
        |------------------- MODULE C -------------------
        |VARIABLE x
        |magic == x /= 2
        |===================================================
        |VARIABLE y
        |C1 == INSTANCE C WITH x <- y
        |===================================================
        |VARIABLE z
        |B1 == INSTANCE B WITH y <- z
        |===================================================""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // expect B1!C1!magic and z
    assert(2 == root.declarations.size)
    val magic = root.declarations
      .find(_.name == "B1!C1!magic")
      .getOrElse(fail("B1!C1!magic not found"))
    assert("B1!C1!magic" == magic.name)
    magic.asInstanceOf[TlaOperDecl].body match {
      case body @ OperEx(TlaOper.ne, NameEx("z"), ValEx(TlaInt(i))) =>
        assert(i == 2)
        assert(sourceStore.contains(body.ID))

      case _ =>
        fail("expected B1!C1!magic == z /= 2")
    }
  }

  // This test works due a temporary bugfix for issue #130.
  // We should test it again, once the bug in SANY is fixed.
  test("RECURSIVE operator inside INSTANCE") {
    val text =
      """---- MODULE recInInstance ----
        |---- MODULE M ----
        |RECURSIVE a(_)
        |a(X) == a(X)
        |================================
        |RECURSIVE b(_)
        |b(X) == b(X)
        |I == INSTANCE M
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(2 == root.declarations.size)
    val b = root.declarations.head
    assert("b" == b.name)
    assert(b.asInstanceOf[TlaOperDecl].isRecursive)
    val aOfM = root.declarations(1)
    // I!a should be recursive
    assert("I!a" == aOfM.name)
    assert(aOfM.asInstanceOf[TlaOperDecl].isRecursive)
  }

  test("instances of standard modules") {
    // Issue #52: the built-in operators are not eliminated when using INSTANCE
    val text =
      """---- MODULE issue52 ----
        |I == INSTANCE Sequences
        |A == I!Append(<<>>, {})
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // the definitions of the standard operators are filtered out
    assert(2 == root.declarations.size)
    root.declarations.find(_.name == "A") match {
      case Some(TlaOperDecl("A", _, body)) =>
        assert(append(tuple(), enumSet()).untyped() == body)

      case d => fail("unexpected declaration: " + d)
    }
  }

  test("operators of local instances of the standard modules") {
    // Issue #295: the built-in operators are not eliminated when using LOCAL INSTANCE
    val text =
      """---- MODULE issue295 ----
        |---- MODULE A ----
        |LOCAL INSTANCE Sequences
        |A == Append(<<>>, {})
        |==================
        |INSTANCE A
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // the definitions of the standard operators are filtered out
    assert(1 == root.declarations.size)
    root.declarations(0) match {
      case TlaOperDecl("A", _, body) =>
        assert(append(tuple(), enumSet()).untyped() == body)

      case d => fail("unexpected declaration: " + d)
    }
  }

  test("values of local instances of the standard modules") {
    // Issue #295: the built-in operators are not eliminated when using LOCAL INSTANCE
    val text =
      """---- MODULE issue295 ----
        |---- MODULE A ----
        |LOCAL INSTANCE Integers
        |A == Int
        |==================
        |INSTANCE A
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // the definitions of the standard operators are filtered out
    assert(1 == root.declarations.size)
    root.declarations(0) match {
      case TlaOperDecl("A", _, body) =>
        assert(ValEx(TlaIntSet) == body)

      case d => fail("unexpected declaration: " + d)
    }
  }

}

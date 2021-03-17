package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.InlinerOfUserOper
import at.forsyte.apalache.tla.lir.{SimpleFormalParam, TestingPredefs}
import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import at.forsyte.apalache.tla.typecheck.{BoolT1, IntT1, OperT1}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestInlinerofUserOper extends FunSuite with TestingPredefs {

  import tla._

  test("Test Inline") {
    val types =
      Map("i" -> IntT1(), "b" -> BoolT1(), "U" -> OperT1(Seq(), IntT1()), "C" -> OperT1(Seq(IntT1()), IntT1()))
    val cBody = plus(n_x ? "i", int(1))
      .typed(types, "i")
    // C(x) == x + 1
    // B == k
    // A == B()
    val cDecl = declOp("C", cBody, SimpleFormalParam("x"))
      .typedOperDecl(types, "C")
    val aDecl = declOp("A", appOp(tla.name("B") ? "U") ? "i")
      .typedOperDecl(types, "U")
    val bDecl = declOp("B", name("k") ? "i")
      .typedOperDecl(types, "C")

    val operDecls = Seq(aDecl, bDecl, cDecl)

    val bodies = BodyMapFactory.makeFromDecls(operDecls)

    val transformation = InlinerOfUserOper(bodies, new IdleTracker())

    // B
    val ex1 = tla
      .name("B")
      .typed(types, "U")
    // B()
    val ex2 = appOp(name("B") ? "U")
      .typed(types, "i")
    // A
    val ex3 = tla
      .name("A")
      .typed(types, "U")
    // A()
    val ex4 = appOp(name("A") ? "U")
      .typed(types, "i")
    // 1 = 0 \/ C(A()) >= 0
    val ex5 = or(
        eql(int(1), int(0)) ? "b",
        ge(appOp(tla.name("C") ? "C", appOp(tla.name("A") ? "U") ? "i") ? "i", int(0)) ? "b"
    )
      .typed(types, "b")
    // LET X == C(p) IN X()
    val ex6 = letIn(
        appOp(tla.name("X") ? "U") ? "i",
        declOp("X", appOp(tla.name("C") ? "C", tla.name("p") ? "i") ? "i")
          .typedOperDecl(types, "U")
    ).typed(types, "i")

    // no inlining, as B is just passed by name
    val expected1 = tla.name("B").typed(types, "U")
    val expected2 = tla.name("k").typed(types, "i")
    val expected3 = tla.name("A").typed(types, "U")
    val expected4 = tla.name("k").typed(types, "i")
    // the bodies of A and C are inlined
    val expected5 = or(
        eql(int(1), int(0)) ? "b",
        ge(plus(tla.name("k") ? "i", int(1)) ? "i", int(0)) ? "b"
    ).typed(types, "b")
    // C is inlined, but X is not
    val expected6 = letIn(
        appOp(tla.name("X") ? "U") ? "i",
        declOp("X", plus(tla.name("p") ? "i", int(1)) ? "i")
          .typedOperDecl(types, "U")
    ).typed(types, "i")

    assert(expected1 == transformation(ex1))
    assert(expected2 == transformation(ex2))
    assert(expected3 == transformation(ex3))
    assert(expected4 == transformation(ex4))
    assert(expected5 == transformation(ex5))
    assert(expected6 == transformation(ex6))

    val applyCwithNoArgs = appOp(tla.name("C") ? "U").typed(types, "i")
    val applyCwithTwoArgs = appOp(tla.name("C") ? "U", tla.name("a") ? "i", tla.name("b") ? "i")
      .typed(types, "i")
    assertThrows[IllegalArgumentException] {
      transformation(applyCwithNoArgs)
    }
    assertThrows[IllegalArgumentException] {
      transformation(applyCwithTwoArgs)
    }
  }
}

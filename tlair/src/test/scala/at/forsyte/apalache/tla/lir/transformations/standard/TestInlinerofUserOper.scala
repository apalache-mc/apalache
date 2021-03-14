package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{NameEx, SimpleFormalParam, TestingPredefs}
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

@RunWith(classOf[JUnitRunner])
class TestInlinerofUserOper extends FunSuite with TestingPredefs with Checkers {

  import tla._

  test("Test Inline") {
    val cDecl = declOp("C", plus(n_x, int(1)), SimpleFormalParam("x")).untypedOperDecl()
    val operDecls = Seq(
        declOp("A", appOp(n_B)).untypedOperDecl(),
        declOp("B", n_c).untypedOperDecl(),
        cDecl
    )

    val bodies = BodyMapFactory.makeFromDecls(operDecls)

    val transformation = InlinerOfUserOper(bodies, new IdleTracker())

    val ex1 = n_B
    val ex2 = appOp(n_B).untyped()
    val ex3 = n_A
    val ex4 = appOp(n_A).untyped()
    val ex5 = or(eql(int(1), int(0)), ge(appDecl(cDecl, appOp(n_A)), int(0))).untyped()
    val ex6 = letIn(
        appOp(NameEx("X")),
        declOp("X", appOp(NameEx("C"), n_p)).untypedOperDecl()
    ).untyped()

    val expected1 = n_B // Operators need to be called with apply
    val expected2 = n_c
    val expected3 = n_A // Operators need to be called with apply
    val expected4 = n_c
    val expected5 = or(
        eql(int(1), int(0)),
        ge(plus(n_c, int(1)), int(0))
    ).untyped()
    val expected6 = letIn(
        appOp(NameEx("X")),
        declOp("X", plus(n_p, int(1))).untypedOperDecl()
    ).untyped()

    val exs = Seq(ex1, ex2, ex3, ex4, ex5, ex6)
    val expected = Seq(expected1, expected2, expected3, expected4, expected5, expected6)
    val actual = exs map transformation

    assert(expected == actual)

    assertThrows[IllegalArgumentException] {
      transformation(appOp(NameEx("C")))
    }
    assertThrows[IllegalArgumentException] {
      transformation(appOp(NameEx("C"), n_a, n_b))
    }
  }
}

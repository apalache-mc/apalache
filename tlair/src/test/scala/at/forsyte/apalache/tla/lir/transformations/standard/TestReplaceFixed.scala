package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.Builder.{appOp, declOp, enumSet, ite, letIn, plus, prime}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.transformations.TlaExTransformation
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{FormalParam, NameEx, OperEx, TestingPredefs, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestReplaceFixed extends FunSuite with TestingPredefs {

  def mkTr(replacedEx: TlaEx, newEx: => TlaEx): TlaExTransformation =
    ReplaceFixed(new IdleTracker())(replacedEx, newEx)

  test("Basic replacement") {
    val ex = n_x
    val tr = mkTr(n_x, n_y)
    assert(tr(ex) == n_y)
  }

  test("Nested replacement") {
    val ex = tla.plus(n_x, n_z)
    val tr = mkTr(n_x, n_y)
    assert(tr(ex) == tla.plus(n_y, n_z))
  }

  test("UID uniqueness") {
    val ex = tla.plus(n_x, n_x)
    val tr = mkTr(n_x, NameEx("y"))

    val assertCond = tr(ex) match {
      case OperEx(TlaArithOper.plus, y1, y2) =>
        y1 == y2 && y1.ID != y2.ID
      case _ => false
    }
    assert(assertCond)
  }

  test("Replace in Let-in") {
    val decl = TlaOperDecl("A", List.empty[FormalParam], n_x)
    val ex = tla.letIn(tla.appDecl(decl), decl)
    val tr = mkTr(n_x, n_y)
    val expectedDecl = TlaOperDecl("A", List.empty[FormalParam], n_y)
    val expectedEx = tla.letIn(tla.appDecl(expectedDecl), expectedDecl)
    assert(tr(ex) == expectedEx)
  }

  test("Old test batch") {
    val transformation = mkTr(n_x, n_y)
    val pa1 = n_x -> n_y
    val pa2 = n_z -> n_z
    val pa3 = prime(n_x) -> prime(n_y)
    val pa4 = ite(n_p, n_x, n_y) -> ite(n_p, n_y, n_y)
    val pa5 = letIn(
        plus(n_z, appOp(n_A)),
        declOp("A", n_q)
    ) -> letIn(
        plus(n_z, appOp(n_A)),
        declOp("A", n_q)
    )
    val pa6 = letIn(
        enumSet(plus(n_x, appOp(n_A)), appOp(n_B, n_x)),
        declOp("A", n_x),
        declOp("B", n_p, "p")
    ) -> letIn(
        enumSet(plus(n_y, appOp(n_A)), appOp(n_B, n_y)),
        declOp("A", n_y),
        declOp("B", n_p, "p")
    )

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
        pa6
    )
    val cmp = expected map { case (k, v) =>
      (v, transformation(k))
    }
    cmp foreach { case (ex, act) =>
      assert(ex == act)
    }
  }
}

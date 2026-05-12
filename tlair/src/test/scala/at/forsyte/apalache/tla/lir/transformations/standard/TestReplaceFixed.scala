package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper, TlaArithOper}
import at.forsyte.apalache.tla.lir.transformations.TlaExTransformation
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestReplaceFixed extends AnyFunSuite {
  import tla._

  def mkTr(replacedEx: TlaEx, newEx: => TlaEx): TlaExTransformation =
    ReplaceFixed(new IdleTracker()).whenEqualsTo(replacedEx, newEx)

  test("Basic replacement") {
    val x = tla.name("x")
    val y = tla.name("y")
    val ex = x
    val tr = mkTr(x, y)
    assert(tr(ex) == y.untyped())
  }

  test("Nested replacement") {
    val x = tla.name("x")
    val y = tla.name("y")
    val z = tla.name("z")
    val ex = tla.plus(x, z)
    val tr = mkTr(x, y)
    assert(tr(ex) == tla.plus(y, z).untyped())
  }

  test("UID uniqueness") {
    val x = tla.name("x")
    def y = NameEx("y")
    val ex = tla.plus(x, x)
    val tr = mkTr(x, y)

    val assertCond = tr(ex) match {
      case OperEx(TlaArithOper.plus, y1, y2) =>
        y1 == y2 && y1.ID != y2.ID
      case _ => false
    }
    assert(assertCond)
  }

  test("Replacement with a partial function") {
    val x = tla.name("x")
    val assignX = tla.assign(tla.prime(x), tla.int(3))
    val eqX = tla.eql(tla.prime(x), tla.int(3))
    val ex = tla.and(assignX, eqX)
    val repl = ReplaceFixed(new IdleTracker()).withFun {
      case OperEx(ApalacheOper.assign, lhs @ OperEx(TlaActionOper.prime, NameEx(_)), rhs) =>
        tla.eql(lhs, rhs)
    }
    assert(repl(ex) == tla.and(eqX, eqX).untyped())
  }

  test("Replace in Let-in") {
    val x = tla.name("x")
    val y = tla.name("y")
    val decl = TlaOperDecl("A", List.empty[OperParam], x)
    val ex = tla.letIn(tla.appDecl(decl), decl)
    val tr = mkTr(x, y)
    val expectedDecl = TlaOperDecl("A", List.empty[OperParam], y)
    val expectedEx = tla.letIn(tla.appDecl(expectedDecl), expectedDecl)
    assert(tr(ex) == expectedEx.untyped())
  }

  test("Old test batch") {
    val A = tla.name("A")
    val B = tla.name("B")
    val p = tla.name("p")
    val q = tla.name("q")
    val x = tla.name("x")
    val y = tla.name("y")
    val z = tla.name("z")

    val transformation = mkTr(x, y)
    val pa1: (TlaEx, TlaEx) = x.untyped() -> y.untyped()
    val pa2: (TlaEx, TlaEx) = z.untyped() -> z.untyped()
    val pa3 = prime(x).untyped() -> prime(y).untyped()
    val pa4 = ite(p, x, y).untyped() -> ite(p, y, y).untyped()
    val pa5 = letIn(
        plus(z, appOp(A)),
        declOp("A", q).untypedOperDecl(),
    ).untyped() -> letIn(
        plus(z, appOp(A)),
        declOp("A", q).untypedOperDecl(),
    ).untyped()
    val pa6 = letIn(
        enumSet(plus(x, appOp(A)), appOp(B, x)),
        declOp("A", x).untypedOperDecl(),
        declOp("B", p, OperParam("p")).untypedOperDecl(),
    ).untyped() -> letIn(
        enumSet(plus(y, appOp(A)), appOp(B, y)),
        declOp("A", y).untypedOperDecl(),
        declOp("B", p, OperParam("p")).untypedOperDecl(),
    ).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
        pa6,
    )
    val cmp = expected.map { case (k, v) =>
      (v, transformation(k))
    }
    cmp.foreach { case (ex, act) =>
      assert(ex == act)
    }
  }
}

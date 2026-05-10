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
    val ex = tla.name("x")
    val tr = mkTr(tla.name("x"), tla.name("y"))
    assert(tr(ex) == tla.name("y").untyped())
  }

  test("Nested replacement") {
    val ex = tla.plus(tla.name("x"), tla.name("z"))
    val tr = mkTr(tla.name("x"), tla.name("y"))
    assert(tr(ex) == tla.plus(tla.name("y"), tla.name("z")).untyped())
  }

  test("UID uniqueness") {
    val ex = tla.plus(tla.name("x"), tla.name("x"))
    val tr = mkTr(tla.name("x"), NameEx("y"))

    val assertCond = tr(ex) match {
      case OperEx(TlaArithOper.plus, y1, y2) =>
        y1 == y2 && y1.ID != y2.ID
      case _ => false
    }
    assert(assertCond)
  }

  test("Replacement with a partial function") {
    val assignX = tla.assign(tla.prime(tla.name("x")), tla.int(3))
    val eqX = tla.eql(tla.prime(tla.name("x")), tla.int(3))
    val ex = tla.and(assignX, eqX)
    val repl = ReplaceFixed(new IdleTracker()).withFun {
      case OperEx(ApalacheOper.assign, lhs @ OperEx(TlaActionOper.prime, NameEx(_)), rhs) =>
        tla.eql(lhs, rhs)
    }
    assert(repl(ex) == tla.and(eqX, eqX).untyped())
  }

  test("Replace in Let-in") {
    val decl = TlaOperDecl("A", List.empty[OperParam], tla.name("x"))
    val ex = tla.letIn(tla.appDecl(decl), decl)
    val tr = mkTr(tla.name("x"), tla.name("y"))
    val expectedDecl = TlaOperDecl("A", List.empty[OperParam], tla.name("y"))
    val expectedEx = tla.letIn(tla.appDecl(expectedDecl), expectedDecl)
    assert(tr(ex) == expectedEx.untyped())
  }

  test("Old test batch") {
    val transformation = mkTr(tla.name("x"), tla.name("y"))
    val pa1: (TlaEx, TlaEx) = tla.name("x").untyped() -> tla.name("y").untyped()
    val pa2: (TlaEx, TlaEx) = tla.name("z").untyped() -> tla.name("z").untyped()
    val pa3 = prime(tla.name("x")).untyped() -> prime(tla.name("y")).untyped()
    val pa4 = ite(tla.name("p"), tla.name("x"), tla.name("y")).untyped() -> ite(tla.name("p"), tla.name("y"), tla.name("y")).untyped()
    val pa5 = letIn(
        plus(tla.name("z"), appOp(tla.name("A"))),
        declOp("A", tla.name("q")).untypedOperDecl(),
    ).untyped() -> letIn(
        plus(tla.name("z"), appOp(tla.name("A"))),
        declOp("A", tla.name("q")).untypedOperDecl(),
    ).untyped()
    val pa6 = letIn(
        enumSet(plus(tla.name("x"), appOp(tla.name("A"))), appOp(tla.name("B"), tla.name("x"))),
        declOp("A", tla.name("x")).untypedOperDecl(),
        declOp("B", tla.name("p"), OperParam("p")).untypedOperDecl(),
    ).untyped() -> letIn(
        enumSet(plus(tla.name("y"), appOp(tla.name("A"))), appOp(tla.name("B"), tla.name("y"))),
        declOp("A", tla.name("y")).untypedOperDecl(),
        declOp("B", tla.name("p"), OperParam("p")).untypedOperDecl(),
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

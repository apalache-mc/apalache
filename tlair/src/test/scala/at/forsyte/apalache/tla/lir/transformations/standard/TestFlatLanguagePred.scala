package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.SimpleFormalParam
import org.scalatest.FunSuite
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.TlaModule

class TestFlatLanguagePred extends FunSuite {
  private var pred = new FlatLanguagePred

  test("a flat expression") {
    val expr = tla.enumSet(tla.int(1), tla.str("abc"), tla.bool(false))
    assert(pred.isExprOk(expr))
  }

  test("a call to a user operator") {
    val expr = tla.enumSet(tla.int(1), tla.str("abc"), tla.bool(false))
    val app = tla.appOp(tla.name("UserOp"), expr)
    assert(!pred.isExprOk(app))
  }

  test("a non-nullary let-in ") {
    val app = tla.appOp(tla.name("UserOp"), tla.int(3))
    val letIn = tla.letIn(app,
      tla.declOp("UserOp",
        tla.plus(tla.int(1), tla.name("x")),
        SimpleFormalParam("x")))
    assert(!pred.isExprOk(app))
  }

  test("a nullary let-in ") {
    val app = tla.appOp(tla.name("UserOp"))
    val letIn = tla.letIn(app,
      tla.declOp("UserOp",
        tla.plus(tla.int(1), tla.int(2))))
    assert(pred.isExprOk(letIn))
  }

  test("nested nullary let-in ") {
    val app = tla.plus(tla.appOp(tla.name("A")), tla.appOp(tla.name("B")))
    val letIn = tla.letIn(app,
      tla.declOp("A",
        tla.plus(tla.int(1), tla.int(2))))
    val outerLetIn =
      tla.letIn(letIn,
        tla.declOp("B",
          tla.int(3)))
    assert(pred.isExprOk(outerLetIn))
  }

  test("a call to a user operator in a module") {
    val appB = tla.appOp(tla.name("B"), tla.int(1))
    val defA = tla.declOp("A", appB)
    val mod = new TlaModule("mod", Seq(defA))
    assert(!pred.isModuleOk(mod))
  }

  test("a module without calls") {
    val appB = tla.int(1)
    val defA = tla.declOp("A", appB)
    val mod = new TlaModule("mod", Seq(defA))
    assert(pred.isModuleOk(mod))
  }
}

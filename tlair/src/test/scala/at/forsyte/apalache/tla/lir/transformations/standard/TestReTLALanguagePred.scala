package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestReTLALanguagePred extends LanguagePredTestSuite {
  private val pred = new ReTLALanguagePred

  import tla._

  test("reTLA: constant expressions") {
    expectOk(pred.isExprOk(name("x")))
    expectOk(pred.isExprOk(prime(name("x"))))
    expectOk(pred.isExprOk(int(22)))
    expectOk(pred.isExprOk(bool(false)))
    expectOk(pred.isExprOk(str("foo")))
    expectOk(pred.isExprOk(booleanSet()))
    expectOk(pred.isExprOk(ValEx(TlaIntSet)))
    expectOk(pred.isExprOk(ValEx(TlaNatSet)))
  }

  test("reTLA: set expressions") {
    expectFail(pred.isExprOk(cup(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(in(int(1), enumSet(int(2)))))
    expectFail(pred.isExprOk(enumSet(int(1))))
    expectFail(pred.isExprOk(subseteq(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(filter(name("x"), enumSet(int(1)), bool(false))))
    expectFail(pred.isExprOk(map(int(2), name("x"), enumSet(int(1)))))

    expectFail(pred.isExprOk(powSet(enumSet(int(1), int(2)))))
    expectFail(pred.isExprOk(union(enumSet(enumSet(int(1), int(2))))))
    expectFail(pred.isExprOk(dotdot(int(10), int(20))))

    expectFail(pred.isExprOk(cap(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(setminus(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(notin(int(1), enumSet(int(2)))))
    expectFail(pred.isExprOk(times(name("X"), name("Y"))))
  }

  test("reTLA: finite set expressions") {
    expectFail(pred.isExprOk(isFin(enumSet(int(1)))))
    expectFail(pred.isExprOk(card(enumSet(int(1)))))
  }

  test("reTLA: function expressions") {
    expectOk(pred.isExprOk(funDef(tla.int(1), name("x"), name("S"))))
    expectOk(pred.isExprOk(appFun(name("f"), int(3))))
    expectOk(pred.isExprOk(appFun(name("f"), tuple(int(3), int(3)))))
    expectOk(pred.isExprOk(except(name("f"), tuple(int(3)), bool(true))))
    expectOk(pred.isExprOk(except(name("f"), tuple(tuple(int(3), int(3))), bool(true))))
    expectFail(pred.isExprOk(funSet(name("X"), name("Y"))))
    expectFail(pred.isExprOk(dom(name("X"))))
  }

  test("reTLA: tuples, records, sequences") {
    expectFail(pred.isExprOk(tuple(int(1), bool(true))))
    expectFail(pred.isExprOk(enumFun(str("a"), bool(true))))
    expectFail(pred.isExprOk(head(tuple(int(1), int(2)))))
    expectFail(pred.isExprOk(tail(tuple(int(1), int(2)))))
    expectFail(pred.isExprOk(subseq(tuple(int(1), int(2)), int(3), int(4))))
    expectFail(pred.isExprOk(len(tuple(int(1), int(2)))))
    expectFail(pred.isExprOk(append(tuple(int(1), int(2)), tuple(int(2), int(3)))))
  }

  test("reTLA: misc.") {
    expectFail(pred.isExprOk(label(int(2), "a")))
    expectFail(pred.isExprOk(label(int(2), "a", "b")))
  }

  test("reTLA: integer expressions") {
    expectFail(pred.isExprOk(lt(int(1), int(3))))
    expectFail(pred.isExprOk(le(int(1), int(3))))
    expectFail(pred.isExprOk(gt(int(1), int(3))))
    expectFail(pred.isExprOk(ge(int(1), int(3))))
    expectFail(pred.isExprOk(plus(int(1), int(3))))
    expectFail(pred.isExprOk(minus(int(1), int(3))))
    expectFail(pred.isExprOk(mult(int(1), int(3))))
    expectFail(pred.isExprOk(div(int(1), int(3))))
    expectFail(pred.isExprOk(mod(int(1), int(3))))
    expectFail(pred.isExprOk(exp(int(2), int(3))))
    expectFail(pred.isExprOk(uminus(int(2))))
  }

  test("reTLA: control expressions") {
    expectOk(pred.isExprOk(ite(name("p"), int(1), int(2))))
    expectFail(pred.isExprOk(caseOther(int(1), bool(false), int(2))))
    expectFail(pred.isExprOk(caseSplit(bool(false), int(2))))
  }

  test("reTLA: record expressions") {
    expectFail(pred.isExprOk(recSet(name("a"), name("A"))))
  }

  test("reTLA: logic expressions") {
    expectOk(pred.isExprOk(or(bool(false), name("b"))))
    expectOk(pred.isExprOk(and(bool(false), name("b"))))
    expectOk(pred.isExprOk(equiv(bool(false), name("b"))))
    expectOk(pred.isExprOk(impl(bool(false), name("b"))))
    expectOk(pred.isExprOk(neql(bool(false), name("b"))))
  }

  /**
   * **************************** the tests for nullary LET-IN ********************************************
   */

  test("a call to a user operator") {
    val expr = str("abc")
    val app = appOp(name("UserOp"), expr)
    expectFail(pred.isExprOk(app))
  }

  test("a non-nullary let-in ") {
    val app = appOp(name("UserOp"), int(3))
    val letInDef = letIn(app, declOp("UserOp", and(bool(true), name("x")), OperParam("x")).untypedOperDecl())
    expectFail(pred.isExprOk(letInDef))
  }

  test("a nullary let-in ") {
    val app = appOp(name("UserOp"))
    val letInDef = letIn(app, declOp("UserOp", and(bool(true), bool(false))).untypedOperDecl())
    expectOk(pred.isExprOk(letInDef))
  }

  test("nested nullary let-in ") {
    val app = and(appOp(name("A")), appOp(name("B")))
    val letInDef = letIn(app, declOp("A", and(bool(true), bool(false))).untypedOperDecl())
    val outerLetIn =
      letIn(letInDef, declOp("B", bool(true)).untypedOperDecl())
    expectOk(pred.isExprOk(outerLetIn))
  }

  test("a call to a user operator in a module") {
    val appB = appOp(name("B"), int(1))
    val defA = declOp("A", appB)
    val mod = new TlaModule("mod", Seq(defA))
    expectFail(pred.isModuleOk(mod))
  }

  test("a module without calls") {
    val appB = int(1)
    val defA = declOp("A", appB)
    val mod = new TlaModule("mod", Seq(defA))
    expectOk(pred.isModuleOk(mod))
  }
}

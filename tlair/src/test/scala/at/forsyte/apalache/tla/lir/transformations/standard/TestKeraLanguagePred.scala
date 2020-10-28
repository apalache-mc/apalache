package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}

class TestKeraLanguagePred extends LanguagePredTestSuite {
  private val pred = new KeraLanguagePred

  import tla._

  test("a KerA constant expression") {
    expectOk(pred.isExprOk(name("x")))
    expectOk(pred.isExprOk(prime(name("x"))))
    expectOk(pred.isExprOk(int(22)))
    expectOk(pred.isExprOk(bool(false)))
    expectOk(pred.isExprOk(str("foo")))
    expectOk(pred.isExprOk(booleanSet()))
    expectOk(pred.isExprOk(ValEx(TlaIntSet)))
    expectOk(pred.isExprOk(ValEx(TlaNatSet)))
  }

  test("a KerA set expression") {
    expectOk(pred.isExprOk(cup(enumSet(int(1)), enumSet(int(2)))))
    expectOk(pred.isExprOk(in(int(1), enumSet(int(2)))))
    expectOk(pred.isExprOk(enumSet(int(1))))
    expectOk(pred.isExprOk(subseteq(enumSet(int(1)), enumSet(int(2)))))
    expectOk(pred.isExprOk(filter("x", enumSet(int(1)), bool(false))))
    expectOk(pred.isExprOk(map(int(2), "x", enumSet(int(1)))))

    expectOk(pred.isExprOk(powSet(enumSet(int(1), int(2)))))
    expectOk(pred.isExprOk(union(enumSet(enumSet(int(1), int(2))))))
    expectOk(pred.isExprOk(dotdot(int(10), int(20))))
  }

  test("a KerA finite set expression") {
    expectOk(pred.isExprOk(isFin(enumSet(int(1)))))
    expectOk(pred.isExprOk(card(enumSet(int(1)))))
  }

  test("a KerA function expression") {
    expectOk(pred.isExprOk(funDef(tla.int(1), name("x"), name("S"))))
    expectOk(pred.isExprOk(appFun(name("f"), int(3))))
    expectOk(pred.isExprOk(except(name("f"), int(3), bool(true))))
    expectOk(pred.isExprOk(funSet(name("X"), name("Y"))))
    expectOk(pred.isExprOk(dom(name("X"))))
  }

  test("KerA tuples, records, sequences") {
    expectOk(pred.isExprOk(tuple(int(1), bool(true))))
    expectOk(pred.isExprOk(enumFun(str("a"), bool(true))))
    expectOk(pred.isExprOk(head(tuple(1, 2))))
    expectOk(pred.isExprOk(tail(tuple(1, 2))))
    expectOk(pred.isExprOk(subseq(tuple(1, 2), 3, 4)))
    expectOk(pred.isExprOk(len(tuple(1, 2))))
    expectOk(pred.isExprOk(append(tuple(1, 2), tuple(2, 3))))
  }

  test("KerA miscellania") {
    expectOk(pred.isExprOk(label(int(2), "a")))
    expectOk(pred.isExprOk(label(int(2), "a", "b")))
    expectOk(pred.isExprOk(withType(name("x"), enumSet(booleanSet()))))
  }

  test("KerA TLC") {
    expectOk(pred.isExprOk(OperEx(TlcOper.print, tla.bool(true), tla.str("msg"))))
    expectOk(pred.isExprOk(OperEx(TlcOper.printT, tla.str("msg"))))
    expectOk(pred.isExprOk(OperEx(TlcOper.assert, tla.bool(true), tla.str("msg"))))
    expectOk(pred.isExprOk(OperEx(TlcOper.colonGreater, tla.int(1), tla.int(2))))
    expectOk(pred.isExprOk(OperEx(TlcOper.atat, NameEx("fun"), NameEx("pair"))))
  }

  test("a KerA integer expression") {
    expectOk(pred.isExprOk(lt(int(1), int(3))))
    expectOk(pred.isExprOk(le(int(1), int(3))))
    expectOk(pred.isExprOk(gt(int(1), int(3))))
    expectOk(pred.isExprOk(ge(int(1), int(3))))
    expectOk(pred.isExprOk(plus(int(1), int(3))))
    expectOk(pred.isExprOk(minus(int(1), int(3))))
    expectOk(pred.isExprOk(mult(int(1), int(3))))
    expectOk(pred.isExprOk(div(int(1), int(3))))
    expectOk(pred.isExprOk(mod(int(1), int(3))))
    expectOk(pred.isExprOk(exp(int(2), int(3))))
    expectOk(pred.isExprOk(uminus(int(2))))
  }

  test("a KerA control expression") {
    expectOk(pred.isExprOk(ite(name("p"), int(1), int(2))))
  }

  test("not a KerA set expression") {
    expectFail(pred.isExprOk(cap(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(setminus(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(notin(int(1), enumSet(int(2)))))
    expectFail(pred.isExprOk(supseteq(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(subset(enumSet(int(1)), enumSet(int(2)))))
    expectFail(pred.isExprOk(supset(enumSet(int(1)), enumSet(int(2)))))
  }

  test("not a KerA record expression") {
    expectFail(pred.isExprOk(recSet(name("a"), name("A"))))
  }

  test("not a KerA tuple expression") {
    expectFail(pred.isExprOk(times(name("X"), name("Y"))))
  }

  test("a KerA logic expression") {
    expectOk(pred.isExprOk(or(bool(false), name("b"))))
    expectOk(pred.isExprOk(and(bool(false), name("b"))))
  }

  test("not a KerA logic expression") {
    expectFail(pred.isExprOk(equiv(bool(false), name("b"))))
    expectFail(pred.isExprOk(impl(bool(false), name("b"))))
    expectFail(pred.isExprOk(neql(bool(false), name("b"))))
  }

  test("not a KerA control expression") {
    expectFail(pred.isExprOk(caseOther(int(1), bool(false), int(2))))
    expectFail(pred.isExprOk(caseSplit(bool(false), int(2))))
  }

  /****************************** the tests from TestFlatLanguagePred *********************************************/

  test("a call to a user operator") {
    val expr = enumSet(int(1), str("abc"), bool(false))
    val app = appOp(name("UserOp"), expr)
    expectFail(pred.isExprOk(app))
  }

  test("a non-nullary let-in ") {
    val app = appOp(name("UserOp"), int(3))
    val letInDef = letIn(app,
      declOp("UserOp",
        plus(int(1), name("x")),
        SimpleFormalParam("x")))
    expectFail(pred.isExprOk(letInDef))
  }

  test("a nullary let-in ") {
    val app = appOp(name("UserOp"))
    val letInDef = letIn(app,
      declOp("UserOp",
        plus(int(1), int(2))))
    expectOk(pred.isExprOk(letInDef))
  }

  test("nested nullary let-in ") {
    val app = plus(appOp(name("A")), appOp(name("B")))
    val letInDef = letIn(app,
      declOp("A",
        plus(int(1), int(2))))
    val outerLetIn =
      letIn(letInDef,
        declOp("B",
          int(3)))
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

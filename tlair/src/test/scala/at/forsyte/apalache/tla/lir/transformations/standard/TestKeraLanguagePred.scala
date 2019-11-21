package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaNatSet}
import org.scalatest.FunSuite

class TestKeraLanguagePred extends FunSuite {
  private val pred = new KeraLanguagePred

  import tla._

  test("a KerA constant expression") {
    assert(pred.isExprOk(name("x")))
    assert(pred.isExprOk(prime(name("x"))))
    assert(pred.isExprOk(int(22)))
    assert(pred.isExprOk(bool(false)))
    assert(pred.isExprOk(str("foo")))
    assert(pred.isExprOk(booleanSet()))
    assert(pred.isExprOk(ValEx(TlaIntSet)))
    assert(pred.isExprOk(ValEx(TlaNatSet)))
  }

  test("a KerA set expression") {
    assert(pred.isExprOk(cup(enumSet(int(1)), enumSet(int(2)))))
    assert(pred.isExprOk(in(int(1), enumSet(int(2)))))
    assert(pred.isExprOk(enumSet(int(1))))
    assert(pred.isExprOk(subseteq(enumSet(int(1)), enumSet(int(2)))))
    assert(pred.isExprOk(filter("x", enumSet(int(1)), bool(false))))
    assert(pred.isExprOk(map(int(2), "x", enumSet(int(1)))))

    assert(pred.isExprOk(powSet(enumSet(int(1), int(2)))))
    assert(pred.isExprOk(union(enumSet(enumSet(int(1), int(2))))))
    assert(pred.isExprOk(dotdot(int(10), int(20))))
  }

  test("a KerA finite set expression") {
    assert(pred.isExprOk(isFin(enumSet(int(1)))))
    assert(pred.isExprOk(card(enumSet(int(1)))))
  }

  test("a KerA function expression") {
    assert(pred.isExprOk(funDef(tla.int(1), name("x"), name("S"))))
    assert(pred.isExprOk(appFun(name("f"), int(3))))
    assert(pred.isExprOk(except(name("f"), int(3), bool(true))))
    assert(pred.isExprOk(funSet(name("X"), name("Y"))))
    assert(pred.isExprOk(dom(name("X"))))
  }

  test("KerA tuples, records, sequences") {
    assert(pred.isExprOk(tuple(int(1), bool(true))))
    assert(pred.isExprOk(enumFun(str("a"), bool(true))))
    assert(pred.isExprOk(head(tuple(1, 2))))
    assert(pred.isExprOk(tail(tuple(1, 2))))
    assert(pred.isExprOk(subseq(tuple(1, 2), 3, 4)))
    assert(pred.isExprOk(len(tuple(1, 2))))
    assert(pred.isExprOk(append(tuple(1, 2), tuple(2, 3))))
  }

  test("KerA miscellania") {
    assert(pred.isExprOk(label(int(2), "a")))
    assert(pred.isExprOk(label(int(2), "a", "b")))
    assert(pred.isExprOk(withType(name("x"), enumSet(booleanSet()))))
  }

  test("KerA TLC") {
    assert(pred.isExprOk(OperEx(TlcOper.print, tla.bool(true), tla.str("msg"))))
    assert(pred.isExprOk(OperEx(TlcOper.printT, tla.str("msg"))))
    assert(pred.isExprOk(OperEx(TlcOper.assert, tla.bool(true), tla.str("msg"))))
    assert(pred.isExprOk(OperEx(TlcOper.colonGreater, tla.int(1), tla.int(2))))
    assert(pred.isExprOk(OperEx(TlcOper.atat, NameEx("fun"), NameEx("pair"))))
  }

  test("a KerA integer expression") {
    assert(pred.isExprOk(lt(int(1), int(3))))
    assert(pred.isExprOk(le(int(1), int(3))))
    assert(pred.isExprOk(gt(int(1), int(3))))
    assert(pred.isExprOk(ge(int(1), int(3))))
    assert(pred.isExprOk(plus(int(1), int(3))))
    assert(pred.isExprOk(minus(int(1), int(3))))
    assert(pred.isExprOk(mult(int(1), int(3))))
    assert(pred.isExprOk(div(int(1), int(3))))
    assert(pred.isExprOk(mod(int(1), int(3))))
    assert(pred.isExprOk(exp(int(2), int(3))))
    assert(pred.isExprOk(uminus(int(2))))
  }

  test("a KerA control expression") {
    assert(pred.isExprOk(ite(name("p"), int(1), int(2))))
  }

  test("not a KerA set expression") {
    assert(!pred.isExprOk(cap(enumSet(int(1)), enumSet(int(2)))))
    assert(!pred.isExprOk(setminus(enumSet(int(1)), enumSet(int(2)))))
    assert(!pred.isExprOk(notin(int(1), enumSet(int(2)))))
    assert(!pred.isExprOk(supseteq(enumSet(int(1)), enumSet(int(2)))))
    assert(!pred.isExprOk(subset(enumSet(int(1)), enumSet(int(2)))))
    assert(!pred.isExprOk(supset(enumSet(int(1)), enumSet(int(2)))))
  }

  test("not a KerA record expression") {
    assert(!pred.isExprOk(recSet(name("a"), name("A"))))
  }

  test("not a KerA tuple expression") {
    assert(!pred.isExprOk(times(name("X"), name("Y"))))
  }

  test("a KerA logic expression") {
    assert(pred.isExprOk(or(bool(false), name("b"))))
    assert(pred.isExprOk(and(bool(false), name("b"))))
  }

  test("not a KerA logic expression") {
    assert(!pred.isExprOk(equiv(bool(false), name("b"))))
    assert(!pred.isExprOk(impl(bool(false), name("b"))))
    assert(!pred.isExprOk(neql(bool(false), name("b"))))
  }

  test("not a KerA control expression") {
    assert(!pred.isExprOk(caseOther(int(1), bool(false), int(2))))
    assert(!pred.isExprOk(caseSplit(bool(false), int(2))))
  }

  /****************************** the tests from TestFlatLanguagePred *********************************************/

  test("a call to a user operator") {
    val expr = enumSet(int(1), str("abc"), bool(false))
    val app = appOp(name("UserOp"), expr)
    assert(!pred.isExprOk(app))
  }

  test("a non-nullary let-in ") {
    val app = appOp(name("UserOp"), int(3))
    val letInDef = letIn(app,
      declOp("UserOp",
        plus(int(1), name("x")),
        SimpleFormalParam("x")))
    assert(!pred.isExprOk(letInDef))
  }

  test("a nullary let-in ") {
    val app = appOp(name("UserOp"))
    val letInDef = letIn(app,
      declOp("UserOp",
        plus(int(1), int(2))))
    assert(pred.isExprOk(letInDef))
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
    assert(pred.isExprOk(outerLetIn))
  }

  test("a call to a user operator in a module") {
    val appB = appOp(name("B"), int(1))
    val defA = declOp("A", appB)
    val mod = new TlaModule("mod", Seq(defA))
    assert(!pred.isModuleOk(mod))
  }

  test("a module without calls") {
    val appB = int(1)
    val defA = declOp("A", appB)
    val mod = new TlaModule("mod", Seq(defA))
    assert(pred.isModuleOk(mod))
  }
}

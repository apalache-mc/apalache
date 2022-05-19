package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestKeramelizerInputLanguagePred extends LanguagePredTestSuite {
  private val pred = new KeramelizerInputLanguagePred

  import tla._

  // typed set to account for Keramelizer's set type checks
  val typed_n_a = fromTlaEx(name("a").as(IntT1))
  val typed_n_b = fromTlaEx(name("b").as(IntT1))
  val typedSet = fromTlaEx(enumSet(int(1), int(2)).as(SetT1(IntT1)))
  val untypedSet = fromTlaEx(enumSet(int(1), int(2)).untyped())

  /**
   * ****************** tests from [[KeraLanguagePred]], except where otherwise noted *****************************
   */

  test("accepts TLA+ constant expressions") {
    expectOk(pred.isExprOk(name("x")))
    expectOk(pred.isExprOk(prime(name("x"))))
    expectOk(pred.isExprOk(int(22)))
    expectOk(pred.isExprOk(bool(false)))
    expectOk(pred.isExprOk(str("foo")))
    expectOk(pred.isExprOk(booleanSet()))
    expectOk(pred.isExprOk(ValEx(TlaIntSet)))
    expectOk(pred.isExprOk(ValEx(TlaNatSet)))
  }

  test("accepts TLA+ set expressions") {
    expectOk(pred.isExprOk(cup(enumSet(int(1)), enumSet(int(2)))))
    expectOk(pred.isExprOk(in(int(1), enumSet(int(2)))))
    expectOk(pred.isExprOk(enumSet(int(1))))
    expectOk(pred.isExprOk(subseteq(enumSet(int(1)), enumSet(int(2)))))
    expectOk(pred.isExprOk(filter(name("x"), enumSet(int(1)), bool(false))))
    expectOk(pred.isExprOk(map(int(2), name("x"), enumSet(int(1)))))

    expectOk(pred.isExprOk(powSet(enumSet(int(1), int(2)))))
    expectOk(pred.isExprOk(union(enumSet(enumSet(int(1), int(2))))))
    expectOk(pred.isExprOk(dotdot(int(10), int(20))))

    // in TLA+, but not in KerA+
    expectOk(pred.isExprOk(cap(typedSet, enumSet(int(2)))))
    expectOk(pred.isExprOk(setminus(typedSet, enumSet(int(2)))))
    expectOk(pred.isExprOk(notin(int(1), enumSet(int(2)))))
  }

  test("accepts TLA+ finite set expressions") {
    expectOk(pred.isExprOk(isFin(enumSet(int(1)))))
    expectOk(pred.isExprOk(card(enumSet(int(1)))))
  }

  test("accepts TLA+ function expressions") {
    expectOk(pred.isExprOk(funDef(tla.int(1), name("x"), name("S"))))
    expectOk(pred.isExprOk(appFun(name("f"), int(3))))
    expectOk(pred.isExprOk(except(name("f"), int(3), bool(true))))
    expectOk(pred.isExprOk(funSet(name("X"), name("Y"))))
    expectOk(pred.isExprOk(dom(name("X"))))
  }

  test("accepts TLA+ tuples, records, sequences") {
    expectOk(pred.isExprOk(tuple(int(1), bool(true))))
    expectOk(pred.isExprOk(enumFun(str("a"), bool(true))))
    expectOk(pred.isExprOk(head(tuple(int(1), int(2)))))
    expectOk(pred.isExprOk(tail(tuple(int(1), int(2)))))
    expectOk(pred.isExprOk(subseq(tuple(int(1), int(2)), int(3), int(4))))
    expectOk(pred.isExprOk(len(tuple(int(1), int(2)))))
    expectOk(pred.isExprOk(append(tuple(int(1), int(2)), tuple(int(2), int(3)))))

    // in TLA+, but not in KerA+
    expectOk(pred.isExprOk(recSet(typed_n_a, typedSet).as(SetT1(IntT1))))
    expectOk(pred.isExprOk(times(typedSet, typedSet)))
  }

  test("accepts TLA+ miscellania") {
    expectOk(pred.isExprOk(label(int(2), "a")))
    expectOk(pred.isExprOk(label(int(2), "a", "b")))
  }

  test("accepts TLA+ integer expressions") {
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

  test("accepts TLA+ control expressions") {
    expectOk(pred.isExprOk(ite(name("p"), int(1), int(2))))

    // in TLA+, but not in KerA+
    expectOk(pred.isExprOk(caseOther(int(1), bool(false), int(2))))
    expectOk(pred.isExprOk(caseSplit(bool(false), int(2))))
  }

  test("accepts TLA+ logic expressions") {
    expectOk(pred.isExprOk(or(bool(false), name("b"))))
    expectOk(pred.isExprOk(and(bool(false), name("b"))))

    // in TLA+, but not in KerA+
    expectOk(pred.isExprOk(equiv(bool(false), name("b"))))
    expectOk(pred.isExprOk(impl(bool(false), name("b"))))
    expectOk(pred.isExprOk(neql(bool(false), name("b"))))
  }

  /**
   * *********** additional tests for [[KeramelizerInputLanguagePred]] ***********
   */
  test("accepts binding expressions where first argument is a name") {
    expectOk(pred.isExprOk(exists(name("a"), bool(true))))
    expectOk(pred.isExprOk(forall(name("a"), bool(true))))
    expectOk(pred.isExprOk(choose(name("a"), name("a"), bool(true))))
    expectOk(pred.isExprOk(filter(name("a"), name("a"), bool(true))))
  }

  test("rejects binding expressions where first argument is not a name") {
    expectFail(pred.isExprOk(exists(int(1), name("A"), bool(true))))
    expectFail(pred.isExprOk(exists(str("a"), name("A"), bool(true))))
    expectFail(pred.isExprOk(forall(int(1), name("A"), bool(true))))
    expectFail(pred.isExprOk(forall(str("a"), name("A"), bool(true))))
    expectFail(pred.isExprOk(choose(int(1), name("a"), bool(true))))
    expectFail(pred.isExprOk(choose(str("a"), name("a"), bool(true))))
    expectFail(pred.isExprOk(filter(int(1), name("a"), bool(true))))
    expectFail(pred.isExprOk(filter(str("a"), name("a"), bool(true))))
  }

  test("rejects operator application where first argument is not a name") {
    expectFail(pred.isExprOk(appOp(int(1))))
  }

  test("rejects Seq(_)") {
    expectFail(pred.isExprOk(seqSet(name("A"))))
  }

  test("checks operators with set-typed arguments") {
    // fails with IntT1 in place of expected SetT1(_)
    expectFail(pred.isExprOk(cap(typed_n_a, natSet())))
    expectFail(pred.isExprOk(setminus(typed_n_a, natSet())))
    expectFail(pred.isExprOk(recSet(typed_n_a, typed_n_b)))
    expectFail(pred.isExprOk(times(typed_n_a, natSet())))
    expectFail(pred.isExprOk(times(natSet(), typed_n_a)))
    expectFail(pred.isExprOk(in(prime(typed_n_a), typed_n_b)))

    // fails with untyped set in place of expected SetT1(_)
    expectFail(pred.isExprOk(cap(untypedSet, natSet())))
    expectFail(pred.isExprOk(setminus(untypedSet, natSet())))
    expectFail(pred.isExprOk(recSet(typed_n_a, untypedSet)))
    expectFail(pred.isExprOk(times(untypedSet, natSet())))
    expectFail(pred.isExprOk(in(prime(typed_n_a), untypedSet)))

    // succeeds with typed SetT1(_)
    expectOk(pred.isExprOk(cap(typedSet, natSet())))
    expectOk(pred.isExprOk(setminus(typedSet, natSet())))
    expectOk(pred.isExprOk(recSet(typed_n_a, typedSet).as(SetT1(IntT1))))
    expectOk(pred.isExprOk(times(typedSet, typedSet)))
    expectOk(pred.isExprOk(in(prime(typed_n_a), typedSet)))
  }

  /**
   * **************************** tests from [[TestFlatLanguagePred]] ********************************************
   */

  test("a call to a user operator") {
    val expr = enumSet(int(1), str("abc"), bool(false))
    val app = appOp(name("UserOp"), expr)
    expectFail(pred.isExprOk(app))
  }

  test("a non-nullary let-in ") {
    val app = appOp(name("UserOp"), int(3))
    val letInDef = letIn(app, declOp("UserOp", plus(int(1), name("x")), OperParam("x")).untypedOperDecl())
    expectFail(pred.isExprOk(letInDef))
  }

  test("a nullary let-in ") {
    val app = appOp(name("UserOp"))
    val letInDef = letIn(app, declOp("UserOp", plus(int(1), int(2))).untypedOperDecl())
    expectOk(pred.isExprOk(letInDef))
  }

  test("nested nullary let-in ") {
    val app = plus(appOp(name("A")), appOp(name("B")))
    val letInDef = letIn(app, declOp("A", plus(int(1), int(2))).untypedOperDecl())
    val outerLetIn =
      letIn(letInDef, declOp("B", int(3)).untypedOperDecl())
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

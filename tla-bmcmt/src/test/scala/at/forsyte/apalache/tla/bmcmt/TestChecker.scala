package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, TlaOperDecl}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestChecker extends FunSuite {
  test("Init, OK") {
    // x' \in {2}
    val initTrans = List(mkAssign("x", 2))
    val nextTrans = List(mkAssign("x", 2))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 0)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init, deadlock") {
    // x' \in {2} /\ x' \in {1}
    val initTrans = List(tla.and(mkAssign("x", 2), mkAssign("x", 1)))
    val nextTrans = List(mkAssign("x", 2))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 0)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init, 2 options, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    val nextTrans = List(mkAssign("x", 2))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 0)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 1)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, deadlock") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x > 3 /\ x' \in {x + 1}
    val nextTrans = List(
      tla.and(tla.gt(tla.name("x"), tla.int(3)),
        mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 1)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next, 10 steps, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 10)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, deadlock") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x < 10 /\ x' \in {x + 1}
    val nextTrans = List(
      tla.and(tla.lt(tla.name("x"), tla.int(10)),
        mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))))
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 10)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next + Inv, 10 steps, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 100
    val inv = tla.lt(tla.name("x"), tla.int(100))
    val checkerInput = new CheckerInput(initTrans, nextTrans, Some(inv))
    // initialize the model checker
    val checker = new Checker(checkerInput, 10)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 10 steps, error") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val checkerInput = new CheckerInput(initTrans, nextTrans, Some(inv))
    // initialize the model checker
    val checker = new Checker(checkerInput, 10)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next, 3 steps, non-determinism but no deadlock") {
    // x' \in {1}
    val initTrans = List(mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 100 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(100)),
                         mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    val checkerInput = new CheckerInput(initTrans, nextTrans, None)
    // initialize the model checker
    val checker = new Checker(checkerInput, 2)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, non-determinism in init and next") {
    // x' \in {0} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 0), mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 10 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(10)),
                         mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    val inv = tla.le(tla.name("x"), tla.int(10)) // x <= 10
    val checkerInput = new CheckerInput(initTrans, nextTrans, Some(inv))
    // initialize the model checker
    val checker = new Checker(checkerInput, 10)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }


  ////////////////////////////////////////////////////////////////////
  private def importTla(name: String, text: String) = {
    val (rootName, modules) = new SanyImporter().loadFromSource(name, Source.fromString(text))
    val mod = expectSingleModule(name, rootName, modules)
    val init = mod.declarations.find(_.name == "Init").get
    val next = mod.declarations.find(_.name == "Next").get
    (mod, init, next)
  }

  private def expectOperatorDeclaration(expectedName: String, idx: Int, mod: TlaModule): TlaOperDecl = {
    mod.declarations(idx) match {
      case decl: TlaOperDecl =>
        assert(expectedName == decl.name)
        decl

      case _ =>
        fail("Expected operator " + expectedName + " at position " + idx)
    }
  }

  // copied from TestSanyImporter
  private def expectSingleModule(expectedRootName: String, rootName: String, modules: Map[String, TlaModule]): TlaModule = {
    assert(expectedRootName == rootName)
    assert(1 <= modules.size)
    val root = modules.get(rootName)
    root match {
      case Some(mod) =>
        mod

      case None =>
        fail("Module " + rootName + " not found")
    }
  }

  private def mkAssign(name: String, value: Int) =
    tla.in(tla.prime(tla.name(name)), tla.enumSet(tla.int(value)))

  private def mkAssign(name: String, rhs: TlaEx) =
    tla.in(tla.prime(tla.name(name)), tla.enumSet(rhs))
}

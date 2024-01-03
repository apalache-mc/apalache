package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.{Binding, StateInvariant}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * An abstract test suite that is parameterized by the snapshot type.
 *
 * @author
 *   Igor Konnov
 *
 * @tparam SnapshotT
 *   the snapshot type
 */
trait TestTransitionExecutorImpl[SnapshotT] extends ExecutorBase[SnapshotT] {

  def nX: TBuilderInstruction = tla.name("x", IntT1)
  def nY: TBuilderInstruction = tla.name("y", IntT1)

  test("constant initialization") { exeCtx: ExecutorContextT =>
    // N' <- 1
    val trex = new TransitionExecutorImpl(Set("N"), Set("x", "y"), exeCtx)
    trex.debug = true
    assert(trex.stepNo == 0)
    val constInit = mkAssign("N", 10)
    trex.initializeConstants(constInit)
    val init = tla.and(mkAssignInt("x", tla.name("N", IntT1)), mkAssign("y", 1))
    // init is a potential transition with index 3 (the index is defined by the input spec)
    val isTranslated = trex.prepareTransition(3, init)
    assert(isTranslated)
    // assume that one of the prepared transitions fires
    trex.pickTransition()
    // advance the computation: forget the non-primed variables, rename primed to non-primed
    trex.nextState()
    assert(trex.stepNo == 1)
    // assert something about the current state
    trex.assertState(tla.eql(nX, tla.int(5)))
    assert(trex.sat(60).contains(false))
  }

  test("push 1 transition") { exeCtx: ExecutorContextT =>
    // y' <- 1 /\ x' <- 1
    val init = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    val trex = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    trex.debug = true
    assert(trex.stepNo == 0)
    // init is a potential transition with index 3 (the index is defined by the input spec)
    val isTranslated = trex.prepareTransition(3, init)
    assert(isTranslated)
    // assume that one of the prepared transitions fires
    trex.pickTransition()
    // advance the computation: forget the non-primed variables, rename primed to non-primed
    trex.nextState()
    assert(trex.stepNo == 1)
    // assert something about the current state
    trex.assertState(tla.eql(nY, tla.int(1)))
    assert(trex.sat(60).contains(true))
  }

  test("check enabled and discard") { exeCtx: ExecutorContextT =>
    // an obviously disabled transition: y' <- 1 /\ y' <- 2
    val init = tla.and(mkAssign("y", 1), tla.eql(tla.prime(nY), tla.int(2)), mkAssign("x", 3))
    val trex = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    trex.debug = true
    assert(trex.stepNo == 0)
    // init is a potential transition with index 3 (the index is defined by the input spec)
    val isTranslated = trex.prepareTransition(1, init)
    assert(isTranslated)
    // check, whether the transition is enabled
    trex.assumeTransition(1)
    assert(trex.sat(60).contains(false))
  }

  test("check an invariant after transition") { exeCtx: ExecutorContextT =>
    // y' <- 1 /\ x' <- 1
    val init = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    val trex = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    trex.debug = true
    assert(trex.stepNo == 0)
    // init is a potential transition with index 3 (the index is defined by the input spec)
    val isTranslated = trex.prepareTransition(3, init)
    assert(isTranslated)
    // assume that the transition has fired
    trex.assumeTransition(3)
    // create a snapshot for a later rollback
    val snapshot = trex.snapshot()
    // assert invariant violation and check it
    val notInv = tla.not(tla.eql(tla.prime(nY), tla.prime(nX)))
    trex.assertState(notInv)
    assert(trex.sat(60).contains(false))
    // rollback the snapshot
    trex.recover(snapshot)
    // now the context is satisfiable again
    assert(trex.sat(60).contains(true))
  }

  test("Init + 3x Next") { exeCtx: ExecutorContextT =>
    // x' <- 1 /\ y' <- 1
    val init: TlaEx = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    // x' <- y /\ y' <- x + y
    val trans1: TlaEx =
      tla.and(mkAssignInt("x", nY), mkAssignInt("y", tla.plus(nX, nY)))
    val trans2: TlaEx = tla.and(mkAssignInt("x", nX), mkAssignInt("y", nY))
    val trex = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    trex.nextState()
    trex.prepareTransition(1, trans1)
    trex.pickTransition()
    trex.nextState()
    trex.prepareTransition(1, trans1)
    trex.pickTransition()
    trex.nextState()
    trex.prepareTransition(1, trans1)
    trex.prepareTransition(2, trans2)
    trex.pickTransition()
    trex.nextState()

    // a decoded counterexample needs the SMT model
    assert(trex.sat(0).contains(true))
    // test the decoded execution
    val decPath = trex.decodedExecution().path
    assert(decPath.length == 5)
    // state 0 is produced by transition 0
    assert(0 == decPath(0)._2)
    assert(Binding().toMap == decPath(0)._1)
    // state 1 is produced by transition 1
    assert(1 == decPath(1)._2)

    def mapWithBuild(pairs: (String, TBuilderInstruction)*): Map[String, TlaEx] =
      pairs.map { case (a, b) => a -> b.build }.toMap

    assert(mapWithBuild("x" -> tla.int(1), "y" -> tla.int(1)) == decPath(1)._1)
    // state 2 is produced by transition 1
    assert(1 == decPath(2)._2)
    assert(mapWithBuild("x" -> tla.int(1), "y" -> tla.int(2)) == decPath(2)._1)
    // state 3 is produced by transition 1
    assert(1 == decPath(3)._2)
    assert(mapWithBuild("x" -> tla.int(2), "y" -> tla.int(3)) == decPath(3)._1)
    // state 4 is produced either by transition 1, or by transition 2
    assert(1 == decPath(4)._2 || 2 == decPath(4)._2)
    assert(mapWithBuild("x" -> tla.int(2), "y" -> tla.int(3)) == decPath(4)._1
      || mapWithBuild("x" -> tla.int(3), "y" -> tla.int(5)) == decPath(4)._1)

    // test the symbolic execution
    val exe = trex.execution
    assert(exe.path.length == 5)
    // check the assertions about the execution states
    // state 0 is not restricted, as there are no parameters

    // state 1 is the state right after Init, that is, Init(state0)
    val state1 = exe.path(1)._1
    assertValid(trex, tla.eql(state1("x").toBuilder, tla.int(1)))
    assertValid(trex, tla.eql(state1("y").toBuilder, tla.int(1)))

    // state 2 is the state Next(Init(state0))
    val state2 = exe.path(2)._1
    assertValid(trex, tla.eql(state2("x").toBuilder, tla.int(1)))
    assertValid(trex, tla.eql(state2("y").toBuilder, tla.int(2)))

    // state 3 is the state Next(Next(Init(state0)))
    val state3 = exe.path(3)._1
    assertValid(trex, tla.eql(state3("x").toBuilder, tla.int(2)))
    assertValid(trex, tla.eql(state3("y").toBuilder, tla.int(3)))

    // state 4 is the state Next(Next(Next(Init(state0)))
    val state4 = exe.path(4)._1
    assertValid(trex, tla.or(tla.eql(state4("x").toBuilder, tla.int(2)), tla.eql(state4("x").toBuilder, tla.int(3))))
    assertValid(trex, tla.or(tla.eql(state4("y").toBuilder, tla.int(3)), tla.eql(state4("y").toBuilder, tla.int(5))))

    // regression in multi-core
    val snapshot = trex.snapshot()
    val savedStepNo = trex.stepNo

    trex.prepareTransition(1, trans1)
    trex.pickTransition()
    trex.nextState()

    trex.recover(snapshot)
    assert(savedStepNo == trex.stepNo)
  }

  test("mayChangeAssertion") { exeCtx: ExecutorContextT =>
    // x' <- 1 /\ y' <- 1
    val init = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    // x' <- x /\ y' <- x + y
    val nextTrans = tla.and(mkAssignInt("x", nX), mkAssignInt("y", tla.plus(nX, nY)))
    // push Init
    val trex = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // check what has changed
    val inv0 = tla.ge(nX, tla.int(3))
    val mayChange0 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(!mayChange0)
    val inv1 = tla.ge(nY, nX)
    val mayChange1 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(mayChange1)
  }

  test("regression on #108") { exeCtx: ExecutorContextT =>
    // y' <- 1
    val init = tla.and(mkAssign("y", 1))
    // y' <- y + 1
    val nextTrans = mkAssignInt("y", tla.plus(nY, tla.int(1)))
    // push Init
    val trex = new TransitionExecutorImpl(Set.empty, Set("y"), exeCtx)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    // The invariant negation does not refer to any variables.
    // We flag that it's satisfiability may change, as it could not be checked before
    val notInv = tla.bool(false)
    val mayChange1 = trex.mayChangeAssertion(1, StateInvariant, 0, notInv)
    assert(mayChange1)
    trex.nextState()
    // apply Next
    trex.prepareTransition(1, nextTrans)
    // this time the invariant's validity should not change
    val mayChange2 = trex.mayChangeAssertion(1, StateInvariant, 0, notInv)
    assert(!mayChange2)
  }

  private def mkAssign(name: String, value: Int): TBuilderInstruction =
    tla.assign(tla.prime(tla.name(name, IntT1)), tla.int(value))

  private def mkAssignInt(name: String, rhs: TBuilderInstruction) =
    tla.assign(tla.prime(tla.name(name, IntT1)), rhs)
}

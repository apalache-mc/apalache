package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard.Renaming
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

/**
 * Test variable renaming.
 */
@RunWith(classOf[JUnitRunner])
class TestRenaming extends FunSuite with BeforeAndAfterEach with TestingPredefs {
  import at.forsyte.apalache.tla.lir.Builder._

  private var renaming = new Renaming(TrackerWithListeners())

  override protected def beforeEach(): Unit = {
    renaming = new Renaming(TrackerWithListeners())
  }

  test("test renaming exists/forall") {
    val original =
      and(exists(n_x, n_S, gt(n_x, int(1))), forall(n_x, n_T, lt(n_x, int(42))))
    ///
    val expected =
      and(exists(name("x_1"), n_S, gt(name("x_1"), int(1))), forall(name("x_2"), n_T, lt(name("x_2"), int(42))))
    val renamed = renaming.renameBindingsUnique(original)
    assert(expected == renamed)
  }

  test("test renaming filter") {
    val original =
      cup(
          filter(name("x"), name("S"), eql(name("x"), int(1))),
          filter(name("x"), name("S"), eql(name("x"), int(2)))
      )
    val expected =
      cup(filter(name("x_1"), name("S"), eql(name("x_1"), int(1))),
          filter(name("x_2"), name("S"), eql(name("x_2"), int(2))))
    val renamed = renaming.renameBindingsUnique(original)
    assert(expected == renamed)
  }

  test("Test renaming LET-IN") {
    // LET p(t) == \A x \in S . R(t,x) IN \E x \in S . p(x)
    val original =
      letIn(
          exists(n_x, n_S, appOp(name("p"), n_x)),
          declOp("p", forall(n_x, n_S, appOp(name("R"), name("t"), n_x)), "t")
      )

    val expected =
      letIn(
          exists(name("x_2"), n_S, appOp(name("p_1"), name("x_2"))),
          declOp("p_1", forall(name("x_1"), n_S, appOp(name("R"), name("t_1"), name("x_1"))), "t_1")
      )

    val actual = renaming(original)

    assert(expected == actual)
  }

  test("Test renaming multiple LET-IN") {
    // LET X == TRUE IN X /\ LET X == FALSE IN X
    val original =
      and(
          letIn(
              appOp(name("X")),
              declOp("X", trueEx)
          ),
          letIn(
              appOp(name("X")),
              declOp("X", falseEx)
          )
      )

    val expected =
      and(
          letIn(
              appOp(name("X_1")),
              declOp("X_1", trueEx)
          ),
          letIn(
              appOp(name("X_2")),
              declOp("X_2", falseEx)
          )
      )

    val actual = renaming(original)

    assert(expected == actual)
  }

}

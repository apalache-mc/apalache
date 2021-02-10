package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestSkolemizationMarker extends FunSuite with BeforeAndAfterEach {
  private var marker = new SkolemizationMarker(TrackerWithListeners())

  override def beforeEach(): Unit = {
    marker = new SkolemizationMarker(TrackerWithListeners())
  }

  test("""mark: \E y \in S: P""") {
    val input = tla.exists(tla.name("y"), tla.name("S"), tla.name("P"))
    val expected = OperEx(BmcOper.skolem, input)

    val output = marker(input)
    assert(expected == output)
  }

  test("""mark: \E y \in S: P /\ \E z \in S: Q""") {
    val left = tla.exists(tla.name("y"), tla.name("S"), tla.name("P"))
    val right = tla.exists(tla.name("z"), tla.name("S"), tla.name("Q"))
    val input = tla.and(left, right)
    val expected = tla.and(OperEx(BmcOper.skolem, left), OperEx(BmcOper.skolem, right))

    val output = marker(input)
    assert(expected == output)
  }

  // see the issue #148
  test("""no mark: x' <- \E y \in S: P""") {
    val input =
      tla.assignPrime(tla.name("x"), tla.exists(tla.name("y"), tla.name("S"), tla.name("P")))

    val output = marker(input)
    assert(input == output)
  }

  test("""mark: Cardinality(S) >= 3""") {
    val input = tla.ge(tla.card(tla.name("S")), tla.int(3))
    val expected = OperEx(BmcOper.constCard, input)
    val output = marker(input)
    assert(expected == output)
  }

  test("""no mark: ~(Cardinality(S) >= 3)""") {
    val input = tla.not(tla.ge(tla.card(tla.name("S")), tla.int(3)))
    val output = marker(input)
    assert(input == output)
  }

  test("""no mark: Cardinality(S) < 3""") {
    val input = tla.lt(tla.card(tla.name("S")), tla.int(3))
    val output = marker(input)
    assert(input == output)
  }

}

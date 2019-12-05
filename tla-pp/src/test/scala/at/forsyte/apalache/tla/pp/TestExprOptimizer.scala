package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestExprOptimizer extends FunSuite with BeforeAndAfterEach {
  private var optimizer = new ExprOptimizer(new UniqueNameGenerator(), TrackerWithListeners())

  override def beforeEach(): Unit = {
    optimizer = new ExprOptimizer(new UniqueNameGenerator(), TrackerWithListeners())
  }

  // an optimization for integer ranges
  test("""e \in a..b ~~> e >= a /\ e <= b (but not if e is x')""") {
    val input = tla.in(tla.name("e"), tla.dotdot(tla.name("a"), tla.name("b")))
    val output = optimizer.apply(input)
    val expected =
      tla.and(
        tla.le(tla.name("a"), tla.name("e")),
        tla.le(tla.name("e"), tla.name("b"))
      ) ///
    assert(expected == output)
  }

}
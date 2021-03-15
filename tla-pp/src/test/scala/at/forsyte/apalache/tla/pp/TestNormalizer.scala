package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import at.forsyte.apalache.tla.typecheck._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestNormalizer extends FunSuite with BeforeAndAfterEach {
  private var normalizer: Normalizer = _
  private val types = Map("b" -> BoolT1())

  override def beforeEach(): Unit = {
    normalizer = new Normalizer(new IdleTracker())
  }

  // TODO: we need a complete coverage. Schedule for #649.

  test("""~FALSE ~~> TRUE""") {
    val input = tla
      .not(tla.bool(true))
      .typed(BoolT1())
    val output = normalizer.apply(input)
    val expected = tla.bool(false).typed()
    assert(expected == output)
  }

  test("""~~x ~~> x""") {
    val input = tla
      .not(tla.not(tla.name("x") ? "b") ? "b")
      .typed(types, "b")
    val output = normalizer.apply(input)
    val expected = tla.name("x").typed(BoolT1())
    assert(expected == output)
  }

  test("""~(x /\ y) ~~> ~x \/ ~y""") {
    val input =
      tla
        .not(tla.and(tla.name("x") ? "b", tla.name("y") ? "b") ? "b")
        .typed(types, "b")
    val output = normalizer.apply(input)
    val expected =
      tla
        .or(tla.not(tla.name("x") ? "b") ? "b", tla.not(tla.name("y") ? "b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""~(x \/ y) ~~> ~x /\ ~y""") {
    val input =
      tla
        .not(tla.and(tla.name("x") ? "b", tla.name("y") ? "b") ? "b")
        .typed(types, "b")
    val output = normalizer.apply(input)
    val expected =
      tla
        .or(tla.not(tla.name("x") ? "b") ? "b", tla.not(tla.name("y") ? "b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }
}

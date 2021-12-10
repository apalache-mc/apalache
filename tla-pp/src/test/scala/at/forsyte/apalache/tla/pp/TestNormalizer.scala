package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.TypedPredefs._
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

  test("""~ IF x THEN y ELSE z ~~> IF x THEN ~y ELSE ~z""") {
    val input = tla
      .not(
          tla.ite(
              tla.name("x") ? "b",
              tla.name("y") ? "b",
              tla.name("z") ? "b"
          ) ? "b"
      )
      .typed(types, "b")

    val output = normalizer.apply(input)

    val expected = tla
      .ite(
          tla.name("x") ? "b",
          tla.not(tla.name("y") ? "b") ? "b",
          tla.not(tla.name("z") ? "b") ? "b"
      )
      .typed(types, "b")

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
        .not(tla.or(tla.name("x") ? "b", tla.name("y") ? "b") ? "b")
        .typed(types, "b")
    val output = normalizer.apply(input)
    val expected =
      tla
        .and(tla.not(tla.name("x") ? "b") ? "b", tla.not(tla.name("y") ? "b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""x => y ~~> ~x \/ y""") {}

  test("""~ (x => y) ~~> x /\ ~y""") {}

  test("""(~FALSE <=> x) ~~> TRUE <=> x""") {}

  test("""~ (~FALSE <=> x) ~~> TRUE \neq x""") {}

  test("""~ \E x \in s . y ~~> \A x \in s . ~y""") {}

  test("""~ \A x \in s . y ~~> \E x \in s . ~y""") {}

  test("""~ (x < y) ~~> x >= y""") {}

  test("""~ (x <= y) ~~> x > y""") {}

  test("""~ (x > y) ~~> x <= y""") {}

  test("""~ (x >= y) ~~> x < y""") {}

  test("""~(x \neq y) ~~> x <=> y""") {}

  test("""~(~FALSE \in s) ~~> ~(TRUE \in s)""") {}

  test("""~<>x ~~> []~x""") {}

  test("""~[]x ~~> <>x""") {}
}

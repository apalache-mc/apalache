package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.lir.IntT1
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
      .not(tla.not(tla.name("x") as BoolT1()) as BoolT1())
      .typed(types, "b")
    val output = normalizer.apply(input)
    val expected = tla.name("x").typed(BoolT1())
    assert(expected == output)
  }

  test("""~ IF x THEN y ELSE z ~~> IF x THEN ~y ELSE ~z""") {
    val input = tla
      .not(
          tla.ite(
              tla.name("x") as BoolT1(),
              tla.name("y") as BoolT1(),
              tla.name("z") as BoolT1()
          ) as BoolT1()
      ) as BoolT1()

    val output = normalizer.apply(input)

    val expected = tla
      .ite(
          tla.name("x") as BoolT1(),
          tla.not(tla.name("y") as BoolT1()) as BoolT1(),
          tla.not(tla.name("z") as BoolT1()) as BoolT1()
      ) as BoolT1()

    assert(expected == output)
  }

  test("""~(x /\ y) ~~> ~x \/ ~y""") {
    val input =
      tla
        .not(tla.and(tla.name("x") as BoolT1(), tla.name("y") as BoolT1()) as BoolT1())
        .typed(types, "b")
    val output = normalizer.apply(input)
    val expected =
      tla
        .or(tla.not(tla.name("x") as BoolT1()) as BoolT1(), tla.not(tla.name("y") as BoolT1()) as BoolT1())
        .typed(types, "b")
    assert(expected == output)
  }

  test("""~(x \/ y) ~~> ~x /\ ~y""") {
    val input =
      tla
        .not(tla.or(tla.name("x") as BoolT1(), tla.name("y") as BoolT1()) as BoolT1())
        .typed(types, "b")
    val output = normalizer.apply(input)
    val expected =
      tla
        .and(tla.not(tla.name("x") as BoolT1()) as BoolT1(), tla.not(tla.name("y") as BoolT1()) as BoolT1())
        .typed(types, "b")
    assert(expected == output)
  }

  test("""x => y ~~> ~x \/ y""") {
    val input =
      tla.impl(tla.name("x") as BoolT1(), tla.name("y") as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla
        .or(tla.not(tla.name("x") as BoolT1()) as BoolT1(), tla.name("y") as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ (x => y) ~~> x /\ ~y""") {
    val input =
      tla.not(tla.impl(tla.name("x") as BoolT1(), tla.name("y") as BoolT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla
        .and(tla.name("x") as BoolT1(), tla.not(tla.name("y") as BoolT1()) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""(~FALSE <=> x) ~~> TRUE = x""") {
    val input =
      tla.equiv(tla.not(tla.bool(false)) as BoolT1(), tla.name("x") as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.eql(tla.bool(true), tla.name("x") as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ (~FALSE <=> x) ~~> TRUE /= x""") {
    val input =
      tla
        .not(tla.equiv(tla.not(tla.bool(false)) as BoolT1(), tla.name("x") as BoolT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.neql(tla.bool(true), tla.name("x") as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ \E x \in s . y ~~> \A x \in s . ~y""") {
    val input =
      tla.not(tla.exists(tla.name("x") as BoolT1(), tla.name("s") as SetT1(IntT1()),
              tla.name("y") as BoolT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.forall(tla.name("x") as BoolT1(), tla.name("s") as SetT1(IntT1()),
          tla.not(tla.name("y") as BoolT1()) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ \A x \in s . y ~~> \E x \in s . ~y""") {
    val input =
      tla.not(tla.forall(tla.name("x") as BoolT1(), tla.name("s") as SetT1(IntT1()),
              tla.name("y") as BoolT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.exists(tla.name("x") as BoolT1(), tla.name("s") as SetT1(IntT1()),
          tla.not(tla.name("y") as BoolT1()) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ (x < y) ~~> x >= y""") {
    val input =
      tla.not(tla.lt(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.ge(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ (x <= y) ~~> x > y""") {
    val input =
      tla.not(tla.le(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.gt(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ (x > y) ~~> x <= y""") {
    val input =
      tla.not(tla.gt(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.le(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~ (x >= y) ~~> x < y""") {
    val input =
      tla.not(tla.ge(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.lt(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~(x /= y) ~~> x = y""") {
    val input =
      tla.not(tla.neql(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.eql(tla.name("x") as IntT1(), tla.name("y") as IntT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~(~FALSE \in s) ~~> ~(TRUE \in s)""") {
    val input =
      tla.not(tla.in(tla.not(tla.bool(false)) as BoolT1(), tla.name("s") as SetT1(BoolT1())) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.not(tla.in(tla.bool(true), tla.name("s") as SetT1(BoolT1())) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""(~FALSE \notin s) ~~> ~(TRUE \in s)""") {
    val input =
      tla.notin(tla.not(tla.bool(false)) as BoolT1(), tla.name("s") as SetT1(BoolT1())) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.not(tla.in(tla.bool(true), tla.name("s") as SetT1(BoolT1())) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""lab(a) :: ~FALSE ~~> lab(a) :: TRUE""") {
    val input = tla.label(tla.not(tla.bool(false)) as BoolT1(), "lab", "a") as BoolT1()
    val output = normalizer.apply(input)
    val expected = tla.label(tla.bool(true), "lab", "a") as BoolT1()
    assert(expected == output)
  }

  test("""~<>x ~~> []~x""") {
    val input =
      tla.not(tla.diamond(tla.name("x") as BoolT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.box(tla.not(tla.name("x") as BoolT1()) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""~[]x ~~> <>~x""") {
    val input =
      tla.not(tla.box(tla.name("x") as BoolT1()) as BoolT1()) as BoolT1()
    val output = normalizer.apply(input)
    val expected =
      tla.diamond(tla.not(tla.name("x") as BoolT1()) as BoolT1()) as BoolT1()
    assert(expected == output)
  }

  test("""unchanged cases""") {
    val expressions = List(
        // x ~> y
        tla.leadsTo(tla.name("x") as BoolT1(), tla.name("y") as BoolT1()) as BoolT1()
        // TODO: Add remaining unchanged scenarios
    )

    expressions.foreach({ expression =>
      val output = normalizer.apply(expression)
      assert(expression == output)

      val negatedExpression = tla.not(expression) as BoolT1()
      val negatedOutput = normalizer.apply(negatedExpression)
      assert(negatedExpression == negatedOutput)
    })
  }
}

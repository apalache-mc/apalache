package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, SetT1}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestExpansionMarker extends AnyFunSuite with BeforeAndAfterEach {
  private val intSetT = SetT1(IntT1)
  private val intFunT = FunT1(IntT1, IntT1)

  private var marker = new ExpansionMarker(TrackerWithListeners())

  override def beforeEach(): Unit = {
    marker = new ExpansionMarker(TrackerWithListeners())
  }

  test("""not marked: x \in SUBSET S""") {
    val input = tla.in(tla.name("x", intSetT), tla.powSet(tla.name("S", intSetT)))
    val output = marker.apply(input)
    assert(output == input.build)
  }

  test("""not marked: x \in [S -> T]""") {
    val input = tla.in(tla.name("x", intFunT), tla.funSet(tla.name("S", intSetT), tla.name("T", intSetT)))
    val output = marker.apply(input)
    assert(output == input.build)
  }

  test("""marked: {{1}} \cup SUBSET S""") {
    val S = tla.name("S", intSetT)
    val input = tla.cup(tla.enumSet(tla.enumSet(tla.int(1))), tla.powSet(S))
    val output = marker.apply(input)
    val expected = tla.cup(tla.enumSet(tla.enumSet(tla.int(1))), tla.expand(tla.powSet(S)))

    assert(expected.build == output)
  }

  // although the optimizing phase should simplify this expression, we like to know what happens, if not
  test("""marked: {} \cup [S -> T]""") {
    val S = tla.name("S", intSetT)
    val T = tla.name("T", intSetT)
    val input = tla.in(
        tla.name("x", intFunT),
        tla.cup(tla.emptySet(intFunT), tla.funSet(S, T)),
    )
    val output = marker.apply(input)
    val expected = tla.in(
        tla.name("x", intFunT),
        tla.cup(tla.emptySet(intFunT), tla.expand(tla.funSet(S, T))),
    )
    assert(expected.build == output)
  }

  test("""marked: \A x \in SUBSET S: P""") {
    val S = tla.name("S", intSetT)
    val input = tla.forall(
        tla.name("x", intSetT),
        tla.powSet(S),
        tla.name("P", BoolT1),
    )

    val output = marker.apply(input)
    val expected = tla.forall(
        tla.name("x", intSetT),
        tla.expand(tla.powSet(S)),
        tla.name("P", BoolT1),
    )

    assert(expected.build == output)
  }

  test("""marked: \E x \in SUBSET S: P""") {
    val S = tla.name("S", intSetT)
    val input = tla.exists(
        tla.name("x", intSetT),
        tla.powSet(S),
        tla.name("P", BoolT1),
    )

    val output = marker.apply(input)
    val expected = tla.exists(
        tla.name("x", intSetT),
        tla.expand(tla.powSet(S)),
        tla.name("P", BoolT1),
    )

    assert(expected.build == output)
  }

  test("""not marked: Skolem(\E x \in SUBSET S: P)""") {
    val input = tla.skolem(tla.exists(
            tla.name("x", intSetT),
            tla.powSet(tla.name("S", intSetT)),
            tla.name("P", BoolT1),
        ))

    val output = marker.apply(input)

    assert(input.build == output)
  }

  test("""not marked: CHOOSE x \in SUBSET S: P""") {
    val input =
      tla.choose(
          tla.name("x", intSetT),
          tla.powSet(tla.name("S", intSetT)),
          tla.name("P", BoolT1),
      )

    val output = marker.apply(input)

    assert(input.build == output)
  }

  // #3385: FoldSet folds over the concrete elements of the set, so the set must be expanded,
  // otherwise a lazily-represented set contributes no elements and the fold silently returns the base value.
  test("""marked: ApaFoldSet(Op, v, SUBSET S)""") {
    val S = tla.name("S", intSetT)
    def op = tla.lambda("A", tla.int(0), tla.param("acc", IntT1), tla.param("x", intSetT))
    val input = tla.foldSet(op, tla.int(0), tla.powSet(S))
    val output = marker.apply(input)
    val expected = tla.foldSet(op, tla.int(0), tla.expand(tla.powSet(S)))
    assert(expected.build == output)
  }

  test("""marked: ApaFoldSet(Op, v, [S -> T])""") {
    val S = tla.name("S", intSetT)
    val T = tla.name("T", intSetT)
    def op = tla.lambda("A", tla.int(0), tla.param("acc", IntT1), tla.param("f", intFunT))
    val input = tla.foldSet(op, tla.int(0), tla.funSet(S, T))
    val output = marker.apply(input)
    val expected = tla.foldSet(op, tla.int(0), tla.expand(tla.funSet(S, T)))
    assert(expected.build == output)
  }
}

package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, SetT1}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestExpansionMarker extends FunSuite with BeforeAndAfterEach {
  private var marker = new ExpansionMarker(TrackerWithListeners())
  val types = Map("S" -> SetT1(IntT1()), "PS" -> SetT1(SetT1(IntT1())), "i" -> IntT1(), "b" -> BoolT1(),
      "f" -> FunT1(IntT1(), IntT1()), "FS" -> SetT1(FunT1(IntT1(), IntT1())))

  override def beforeEach(): Unit = {
    marker = new ExpansionMarker(TrackerWithListeners())
  }

  test("""not marked: x \in SUBSET S""") {
    val input =
      tla
        .in(tla.name("x") ? "S", tla.powSet(tla.name("S") ? "S") ? "PS")
        .typed(types, "b")
    val output = marker.apply(input)
    assert(output == input)
  }

  test("""not marked: x \in [S -> T]""") {
    val input = tla
      .in(tla.name("x") ? "f", tla.funSet(tla.name("S") ? "S", tla.name("T") ? "S") ? "FS")
      .typed(types, "b")
    val output = marker.apply(input)
    assert(output == input)
  }

  test("""marked: {1} \cup SUBSET S""") {
    val input = tla
      .cup(tla.enumSet(tla.int(1)) ? "S", tla.powSet(tla.name("S") ? "S") ? "PS")
      .typed(types, "S")
    val output = marker.apply(input)
    val expected = {
      tla
        .cup(tla.enumSet(tla.int(1)) ? "S", tla.apalacheExpand(tla.powSet(tla.name("S") ? "S") ? "PS") ? "PS")
        .typed(types, "S")
    }

    assert(expected == output)
  }

  // although the optimizing phase should simplify this expression, we like to know what happens, if not
  test("""marked: {} \cup [S -> T]""") {
    val input = tla
      .in(tla.name("x") ? "f",
          tla.cup(tla.emptySet() ? "FS", tla.funSet(tla.name("S") ? "S", tla.name("T") ? "S") ? "FS") ? "FS")
      .typed(types, "b")
    val output = marker.apply(input)
    val expected =
      tla
        .in(tla.name("x") ? "f",
            tla.cup(tla.emptySet() ? "FS",
                tla.apalacheExpand(tla.funSet(tla.name("S") ? "S", tla.name("T") ? "S") ? "FS") ? "FS") ? "FS")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""marked: \A x \in SUBSET S: P""") {
    val input = tla
      .forall(
          tla.name("x") ? "S",
          tla.powSet(tla.name("S") ? "S") ? "PS",
          tla.name("P") ? "b"
      )
      .typed(types, "b")

    val output = marker.apply(input)
    val expected = tla
      .forall(
          tla.name("x") ? "S",
          tla.apalacheExpand(tla.powSet(tla.name("S") ? "S") ? "PS") ? "PS",
          tla.name("P") ? "b"
      )
      .typed(types, "b")

    assert(expected == output)
  }

  test("""marked: \E x \in SUBSET S: P""") {
    val input = tla
      .exists(
          tla.name("x") ? "S",
          tla.powSet(tla.name("S") ? "S") ? "PS",
          tla.name("P") ? "b"
      )
      .typed(types, "b")

    val output = marker.apply(input)
    val expected = tla
      .exists(
          tla.name("x") ? "S",
          tla.apalacheExpand(tla.powSet(tla.name("S") ? "S") ? "PS") ? "PS",
          tla.name("P") ? "b"
      )
      .typed(types, "b")

    assert(expected == output)
  }

  test("""not marked: Skolem(\E x \in SUBSET S: P)""") {
    val input =
      tla
        .apalacheSkolem(
            tla.exists(
                tla.name("x") ? "S",
                tla.powSet(tla.name("S") ? "S") ? "PS",
                tla.name("P") ? "b"
            ) ? "b")
        .typed(types, "b")

    val output = marker.apply(input)

    assert(input == output)
  }

  test("""not marked: CHOOSE x \in SUBSET S: P""") {
    val input =
      tla
        .choose(
            tla.name("x") ? "i",
            tla.powSet(tla.name("S") ? "S") ? "PS",
            tla.name("P") ? "b"
        )
        .typed(types, "i")

    val output = marker.apply(input)

    assert(input == output)
  }
}

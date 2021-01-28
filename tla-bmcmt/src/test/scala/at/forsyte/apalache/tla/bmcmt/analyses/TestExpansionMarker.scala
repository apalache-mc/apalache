package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestExpansionMarker extends FunSuite with BeforeAndAfterEach {
  private var marker = new ExpansionMarker(TrackerWithListeners())

  override def beforeEach(): Unit = {
    marker = new ExpansionMarker(TrackerWithListeners())
  }

  test("""not marked: x \in SUBSET S""") {
    val input = tla.in(tla.name("x"), tla.powSet(tla.name("S")))
    val output = marker.apply(input)
    assert(output == input)
  }

  test("""not marked: x \in [S -> T]""") {
    val input = tla.in(tla.name("x"), tla.funSet(tla.name("S"), tla.name("T")))
    val output = marker.apply(input)
    assert(output == input)
  }

  test("""marked: {1} \cup SUBSET S""") {
    val input = tla.cup(tla.enumSet(tla.int(1)), tla.powSet(tla.name("S")))
    val output = marker.apply(input)
    val expected =
      tla.cup(
        tla.enumSet(tla.int(1)),
        OperEx(BmcOper.expand, tla.powSet(tla.name("S"))))

    assert(expected == output)
  }

  // although the optimizing phase should simplify this expression, we like to know what happens, if not
  test("""marked: {} \cup [S -> T]""") {
    val input = tla.in(
      tla.name("x"),
      tla.cup(tla.emptySet(),
        tla.funSet(tla.name("S"), tla.name("T"))))
    val output = marker.apply(input)
    val expected = tla.in(
      tla.name("x"),
      tla.cup(tla.emptySet(),
        OperEx(BmcOper.expand,
          tla.funSet(tla.name("S"), tla.name("T")))))

    assert(expected == output)
  }

  test("""marked: \A x \in SUBSET S: P""") {
    val input = tla.forall(
      tla.name("x"),
      tla.powSet(tla.name("S")),
      tla.name("P")
    ) ///

    val output = marker.apply(input)
    val expected = tla.forall(
      tla.name("x"),
      OperEx(BmcOper.expand, tla.powSet(tla.name("S"))),
      tla.name("P")
    ) ///

    assert(expected == output)
  }

  test("""marked: \E x \in SUBSET S: P""") {
    val input = tla.exists(
      tla.name("x"),
      tla.powSet(tla.name("S")),
      tla.name("P")
    ) ///

    val output = marker.apply(input)
    val expected = tla.exists(
      tla.name("x"),
      OperEx(BmcOper.expand, tla.powSet(tla.name("S"))),
      tla.name("P")
    ) ///

    assert(expected == output)
  }

  test("""not marked: Skolem(\E x \in SUBSET S: P)""") {
    val input =
      OperEx(BmcOper.skolem,
        tla.exists(
          tla.name("x"),
          tla.powSet(tla.name("S")),
          tla.name("P")
        )) ///

    val output = marker.apply(input)

    assert(input == output)
  }

  test("""not marked: x \in {} <: {[Int -> Int]}""") {
    val input =
      tla.exists(
        tla.name("x"),
        OperEx(BmcOper.withType,
          tla.enumSet(),
          tla.enumSet(tla.funSet(tla.intSet(), tla.intSet()))
        ),
        tla.bool(true)
      ) //

    val output = marker.apply(input)

    assert(input == output)
  }

  test("""not marked: \CHOOSE x \in SUBSET S: P""") {
    val input =
        tla.choose(
          tla.name("x"),
          tla.powSet(tla.name("S")),
          tla.name("P")
        ) ///

    val output = marker.apply(input)

    assert(input == output)
  }
}
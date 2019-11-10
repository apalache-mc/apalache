package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

import at.forsyte.apalache.tla.lir.convenience._

@RunWith(classOf[JUnitRunner])
class TestKeramelizer extends FunSuite with BeforeAndAfterEach {
  private var keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())

  override def beforeEach(): Unit = {
    keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())
  }

  test("""X \intersect Y""") {
    val input = tla.cap(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.filter(tla.name("t_1"),
      tla.name("X"),
      tla.in(tla.name("t_1"), tla.name("Y")))
    assert(expected == output)
  }

  test("intersect under another expression") {
    val input =
      tla.cup(tla.name("Z"),
        tla.cap(tla.name("X"), tla.name("Y")))
    val output = keramelizer.apply(input)
    val transformed =
      tla.filter(tla.name("t_1"),
        tla.name("X"),
        tla.in(tla.name("t_1"), tla.name("Y")))
    val expected = tla.cup(tla.name("Z"), transformed)
    assert(expected == output)
  }

  test("""X \ Y""") {
    val input = tla.setminus(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.filter(tla.name("t_1"),
      tla.name("X"),
      tla.not(tla.in(tla.name("t_1"), tla.name("Y"))))
    assert(expected == output)
  }

  test("""x \notin Y ~~> ~(x \in Y)""") {
    val input = tla.notin(tla.name("x"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.not(tla.in(tla.name("x"), tla.name("Y")))
    assert(expected == output)
  }

  test("""a <=> b ~~> a = b""") {
    val input = tla.equiv(tla.name("a"), tla.name("b"))
    val output = keramelizer.apply(input)
    val expected = tla.eql(tla.name("a"), tla.name("b"))
    assert(expected == output)
  }

  test("""a => b ~~> ~a \/ b""") {
    val input = tla.impl(tla.name("a"), tla.name("b"))
    val output = keramelizer.apply(input)
    val expected = tla.or(tla.not(tla.name("a")), tla.name("b"))
    assert(expected == output)
  }

  test("""a /= b ~~> ~(a = b)""") {
    val input = tla.neql(tla.name("a"), tla.name("b"))
    val output = keramelizer.apply(input)
    val expected = tla.not(tla.eql(tla.name("a"), tla.name("b")))
    assert(expected == output)
  }

  test("""[a: A, b: B] ~~> {[a |-> t_1, b |-> t_2]: t_1 \in A, t_2 \in B}""") {
    val input = tla.recSet(tla.name("a"), tla.name("A"), tla.name("b"), tla.name("B"))
    val output = keramelizer.apply(input)
    val rec = tla.enumFun(tla.name("a"), tla.name("t_1"), tla.name("b"), tla.name("t_2"))
    val expected = tla.map(rec, tla.name("t_1"), tla.name("A"), tla.name("t_2"), tla.name("B"))
    assert(expected == output)
  }

  test("""A \X B ~~> {<<t_1, t_2>>: t_1 \in A, t_2 \in B}""") {
    val input = tla.times(tla.name("A"), tla.name("B"))
    val output = keramelizer.apply(input)
    val tup = tla.tuple(tla.name("t_1"), tla.name("t_2"))
    val expected = tla.map(tup, tla.name("t_1"), tla.name("A"), tla.name("t_2"), tla.name("B"))
    assert(expected == output)
  }

}
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

  test("""X \supseteq Y ~~> Y \subseteq X""") {
    val input = tla.supseteq(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.subseteq(tla.name("Y"), tla.name("X"))
    assert(expected == output)
  }

  test("""X \subset Y ~~> ~(X = Y) /\ X \subseteq Y""") {
    val input = tla.subset(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected =
      tla.and(
        tla.not(tla.eql(tla.name("X"), tla.name("Y"))),
        tla.subseteq(tla.name("X"), tla.name("Y"))
      ) ///
    assert(expected == output)
  }

  test("""X \supset Y ~~> ~(X = Y) /\ Y \subseteq X""") {
    val input = tla.supset(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected =
      tla.and(
        tla.not(tla.eql(tla.name("X"), tla.name("Y"))),
        tla.subseteq(tla.name("Y"), tla.name("X"))
      ) ///
    assert(expected == output)
  }

  test("""CASE-OTHER""") {
    val input = tla.caseOther(tla.name("e_def"),
      tla.name("p_1"), tla.name("e_1"),
      tla.name("p_2"), tla.name("e_2"))
    val output = keramelizer.apply(input)
    val expected =
      tla.ite(tla.name("p_1"), tla.name("e_1"),
        tla.ite(tla.name("p_2"), tla.name("e_2"),
          tla.name("e_def")
        ) ///
    ) ///
    assert(expected == output)
  }

  test("""CASE without OTHER""") {
    val input = tla.caseSplit(
      tla.name("p_1"), tla.name("e_1"),
      tla.name("p_2"), tla.name("e_2")
    ) ///
    assertThrows[NotInKeraError](keramelizer.apply(input))
  }

  // we simplify assignments into existential quantification
  test("""x' \in S ~~> \E t_1 \in S: x' = t_1""") {
    val input = tla.in(tla.prime(tla.name("x")), tla.name("S"))
    val output = keramelizer.apply(input)
    val expected =
      tla.exists(
        tla.name("t_1"),
        tla.name("S"),
        tla.eql(tla.prime(tla.name("x")), tla.name("t_1"))
      ) ////
    assert(expected == output)
  }

  test("""x' \in SUBSET S ~~> \E t_1 \in SUBSET S: x' = t_1""") {
    val input = tla.in(tla.prime(tla.name("x")), tla.powSet(tla.name("S")))
    val output = keramelizer.apply(input)
    val expected =
      tla.exists(
        tla.name("t_1"),
        tla.powSet(tla.name("S")),
        tla.eql(tla.prime(tla.name("x")), tla.name("t_1"))
      ) ////
    assert(expected == output)
  }

  test("""x' \in [S -> T] ~~> \E t_1 \in [S -> T]: x' = t_1""") {
    val funSet = tla.funSet(tla.name("S"), tla.name("T"))
    val input = tla.in(tla.prime(tla.name("x")), funSet)
    val output = keramelizer.apply(input)
    val expected =
      tla.exists(
        tla.name("t_1"),
        funSet,
        tla.eql(tla.prime(tla.name("x")), tla.name("t_1"))
      ) ////
    assert(expected == output)
  }

}
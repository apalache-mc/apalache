package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, RecT1, SetT1, StrT1, TlaEx, TupT1}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.TypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestKeramelizer extends FunSuite with BeforeAndAfterEach {
  private var keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())

  override def beforeEach(): Unit = {
    keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())
  }

  test("""X \intersect Y""") {
    val types = Map("e" -> IntT1(), "s" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .cap(tla.name("X") ? "s", tla.name("Y") ? "s")
      .typed(types, "s")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .filter(tla.name("t_1") ? "e", tla.name("X") ? "s", tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b")
        .typed(types, "s")
    assert(expected == output)
  }

  test("intersect under another expression") {
    val types = Map("s" -> SetT1(IntT1()), "e" -> IntT1(), "b" -> BoolT1())
    val input =
      tla
        .cup(tla.name("Z") ? "s", tla.cap(tla.name("X") ? "s", tla.name("Y") ? "s") ? "s")
        .typed(types, "s")
    val output = keramelizer.apply(input)
    val transformed =
      tla.filter(tla.name("t_1") ? "e", tla.name("X") ? "s", tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b")
    val expected =
      tla
        .cup(tla.name("Z") ? "s", transformed ? "s")
        .typed(types, "s")
    assert(expected == output)
  }

  test("""X \ Y""") {
    val types = Map("s" -> SetT1(IntT1()), "e" -> IntT1(), "b" -> BoolT1())
    val input = tla
      .setminus(tla.name("X") ? "s", tla.name("Y") ? "s")
      .typed(types, "s")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .filter(tla.name("t_1") ? "e", tla.name("X") ? "s",
            tla.not(tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b") ? "b")
        .typed(types, "s")
    assert(expected == output)
  }

  test("""x \notin Y ~~> ~(x \in Y)""") {
    val types = Map("s" -> SetT1(IntT1()), "e" -> IntT1(), "b" -> BoolT1())
    val input = tla
      .notin(tla.name("x") ? "e", tla.name("Y") ? "s")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .not(tla.in(tla.name("x") ? "e", tla.name("Y") ? "s") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""a <=> b ~~> a = b""") {
    val types = Map("i" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .equiv(tla.name("a") ? "i", tla.name("b") ? "i")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .eql(tla.name("a") ? "i", tla.name("b") ? "i")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""a => b ~~> ~a \/ b""") {
    val types = Map("b" -> BoolT1())
    val input = tla
      .impl(tla.name("a") ? "b", tla.name("b") ? "b")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .or(tla.not(tla.name("a") ? "b") ? "b", tla.name("b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""a /= b ~~> ~(a = b)""") {
    val types = Map("b" -> BoolT1())
    val input = tla
      .neql(tla.name("a") ? "b", tla.name("b") ? "b")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .not(tla.eql(tla.name("a") ? "b", tla.name("b") ? "b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""[a: A, b: B] ~~> {[a |-> t_1, b |-> t_2]: t_1 \in A, t_2 \in B}""") {
    val types = Map("a" -> BoolT1(), "b" -> StrT1(), "A" -> SetT1(BoolT1()), "B" -> SetT1(StrT1()), "s" -> StrT1(),
        "r" -> RecT1("a" -> BoolT1(), "b" -> StrT1()), "R" -> SetT1(RecT1("a" -> BoolT1(), "b" -> StrT1())))
    val input =
      tla
        .recSet(tla.name("a") ? "s", tla.name("A") ? "A", tla.name("b") ? "s", tla.name("B") ? "B")
        .typed(types, "R")
    val output = keramelizer.apply(input)
    val rec = tla.enumFun(tla.name("a") ? "s", tla.name("t_1") ? "a", tla.name("b") ? "s", tla.name("t_2") ? "b")
    val expected =
      tla
        .map(rec ? "r", tla.name("t_1") ? "a", tla.name("A") ? "A", tla.name("t_2") ? "b", tla.name("B") ? "B")
        .typed(types, "R")
    assert(expected == output)
  }

  test("""A \X B ~~> {<<t_1, t_2>>: t_1 \in A, t_2 \in B}""") {
    val types = Map("a" -> BoolT1(), "b" -> StrT1(), "A" -> SetT1(BoolT1()), "B" -> SetT1(StrT1()),
        "t" -> SetT1(TupT1(BoolT1(), StrT1())), "T" -> SetT1(TupT1(BoolT1(), StrT1())))
    val input =
      tla
        .times(tla.name("A") ? "A", tla.name("B") ? "B")
        .typed(types, "T")
    val output = keramelizer.apply(input)
    val tup = tla.tuple(tla.name("t_1") ? "a", tla.name("t_2") ? "b")
    val expected =
      tla
        .map(tup ? "t", tla.name("t_1") ? "a", tla.name("A") ? "A", tla.name("t_2") ? "b", tla.name("B") ? "B")
        .typed(types, "T")
    assert(expected == output)
  }

  test("""CASE-OTHER""") {
    val types = Map("b" -> BoolT1(), "i" -> IntT1())
    val input = tla
      .caseOther(tla.name("e_def") ? "i", tla.name("p_1") ? "b", tla.name("e_1") ? "i", tla.name("p_2") ? "b",
          tla.name("e_2") ? "i")
      .typed(types, "i")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .ite(tla.name("p_1") ? "b", tla.name("e_1") ? "i",
            tla.ite(tla.name("p_2") ? "b", tla.name("e_2") ? "i", tla.name("e_def") ? "i") ? "b")
        .typed(types, "i")
    assert(expected == output)
  }

  test("""CASE without OTHER""") {
    val types = Map("b" -> BoolT1(), "i" -> IntT1())
    val input = tla.caseSplit(
        tla.name("p_1") ? "b",
        tla.name("e_1") ? "i",
        tla.name("p_2") ? "b",
        tla.name("e_2") ? "i"
    ) ///
    assertThrows[NotInKeraError](keramelizer.apply(input.typed(types, "i")))
  }

  // we simplify assignments into existential quantification
  test("""x' \in S ~~> \E t_1 \in S: x' = t_1""") {
    val types = Map("b" -> BoolT1(), "e" -> IntT1(), "S" -> SetT1(IntT1()))
    val input = tla
      .in(tla.prime(tla.name("x") ? "e") ? "e", tla.name("S") ? "S")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .exists(tla.name("t_1") ? "e", tla.name("S") ? "S",
            tla.eql(tla.prime(tla.name("x") ? "e") ? "e", tla.name("t_1") ? "e") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""x' \in SUBSET S ~~> \E t_1 \in SUBSET S: x' = t_1""") {
    val types = Map("b" -> BoolT1(), "S" -> SetT1(IntT1()), "PS" -> SetT1(SetT1(IntT1())))
    val input =
      tla
        .in(tla.prime(tla.name("x") ? "S") ? "S", tla.powSet(tla.name("S") ? "S") ? "PS")
        .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .exists(tla.name("t_1") ? "S", tla.powSet(tla.name("S") ? "S") ? "PS",
            tla.eql(tla.prime(tla.name("x") ? "S") ? "S", tla.name("t_1") ? "S") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""x' \in [S -> T] ~~> \E t_1 \in [S -> T]: x' = t_1""") {
    val types = Map("b" -> BoolT1(), "S" -> SetT1(IntT1()), "T" -> SetT1(StrT1()), "f" -> FunT1(IntT1(), StrT1()),
        "Sf" -> SetT1(FunT1(IntT1(), StrT1())))
    val funSet = tla.funSet(tla.name("S") ? "S", tla.name("T") ? "T") ? "Sf"
    val input = tla
      .in(tla.prime(tla.name("x") ? "f") ? "f", funSet)
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .exists(tla.name("t_1") ? "f", funSet,
            tla.eql(tla.prime(tla.name("x") ? "f") ? "f", tla.name("t_1") ? "f") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

}

package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, OperT1, RecT1, SetT1}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.TypedPredefs._
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
    val types = Map("b" -> BoolT1(), "i" -> IntT1(), "S" -> SetT1(IntT1()))
    val input =
      tla
        .in(tla.name("e") ? "i", tla.dotdot(tla.name("a") ? "i", tla.name("b") ? "i") ? "S")
        .typed(types, "b")
    val output = optimizer.apply(input)
    val expected =
      tla
        .and(tla.le(tla.name("a") ? "i", tla.name("e") ? "i") ? "b",
            tla.le(tla.name("e") ? "i", tla.name("b") ? "i") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  // an optimization for record accesses
  test("""[a |-> 1, b |-> 2].a becomes 2""") {
    val types = Map("r" -> RecT1("a" -> IntT1(), "b" -> IntT1()), "i" -> IntT1())
    val record =
      tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.int(2))
    val input = tla
      .appFun(record ? "r", tla.str("b"))
      .typed(types, "i")
    val output = optimizer.apply(input)
    val expected = tla.int(2).typed()
    assert(expected == output)
  }

  // an optimization for set comprehensions (maps)
  test("""\E x \in {foo[y]: y \in {1, 2}}: z = x ~~> \E y \in {1, 2}: z = foo[y]""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "f" -> FunT1(IntT1(), BoolT1()), "b" -> BoolT1(),
        "B" -> SetT1(BoolT1()))
    val set12 = tla.enumSet(tla.int(1), tla.int(2)) ? "S"
    val funApp = tla.appFun(tla.name("foo") ? "f", tla.name("y") ? "i") ? "b"
    val map = tla.map(funApp, tla.name("y") ? "i", set12) ? "B"
    val input =
      tla
        .exists(tla.name("x") ? "S", map, tla.eql(tla.name("z") ? "i", tla.name("x") ? "B") ? "b")
        .typed(types, "b")
    val output = optimizer.apply(input)
    val eq = tla.eql(tla.name("z") ? "b", funApp) ? "b"
    val expected =
      tla
        .exists(tla.name("y") ? "i", set12, eq)
        .typed(types, "b")
    assert(expected == output)
  }

  // an optimization for set comprehensions (filters)
  test("""\E x \in {y \in {1, 2}: y = 1}: z = x ~~> \E y \in {1, 2}: z = y /\ y = 1""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1(), "B" -> SetT1(BoolT1()))
    val set12 = tla.enumSet(tla.int(1), tla.int(2)) ? "S"
    val filter =
      tla.filter(tla.name("y") ? "i", set12, tla.eql(tla.name("y") ? "i", tla.int(1) ? "i") ? "b") ? "B"
    val input =
      tla
        .exists(tla.name("x") ? "b", filter, tla.eql(tla.name("z") ? "i", tla.name("x") ? "b") ? "b")
        .typed(types, "b")
    val output = optimizer.apply(input)
    val y_eq_1 = tla.eql(tla.name("y") ? "i", tla.int(1)) ? "b"
    val z_eq_y = tla.eql(tla.name("z") ? "i", tla.name("y") ? "i") ? "b"
    val expected =
      tla
        .exists(tla.name("y") ? "i", set12, tla.and(y_eq_1, z_eq_y) ? "b")
        .typed(types, "b")

    assert(expected == output)
  }

  // optimizations for set cardinalities

  test("""Cardinality(S) = 0 becomes S = {}""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .eql(tla.card(tla.name("S") ? "S") ? "i", tla.int(0))
      .typed(types, "b")
    val output = optimizer.apply(input)
    val expected =
      tla
        .eql(tla.name("S") ? "S", tla.enumSet() ? "S")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""Cardinality(S) > 0 becomes ~(S = {})""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .gt(tla.card(tla.name("S") ? "S") ? "i", tla.int(0))
      .typed(types, "b")
    val output = optimizer.apply(input)
    val expected =
      tla
        .not(tla.eql(tla.name("S") ? "S", tla.enumSet() ? "S") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""Cardinality(S) >= 1 becomes ~(S = {})""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .ge(tla.card(tla.name("S") ? "S") ? "i", tla.int(1))
      .typed(types, "b")
    val output = optimizer.apply(input)
    val expected =
      tla
        .not(tla.eql(tla.name("S") ? "S", tla.enumSet() ? "S") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""Cardinality(S) /= 0 becomes ~(S = {})""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .ge(tla.card(tla.name("S") ? "S") ? "i", tla.int(1))
      .typed(types, "b")
    val output = optimizer.apply(input)
    val expected =
      tla
        .not(tla.eql(tla.name("S") ? "S", tla.enumSet() ? "S") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""Cardinality(S) >= 2 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_2 \in t_3: t_1 /= t_2""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1(), "L" -> OperT1(Seq(), IntT1()))
    val set = tla.name("S") ? "S"
    val input = tla
      .ge(tla.card(set) ? "i", tla.int(2))
      .typed(types, "b")
    val output = optimizer.apply(input)
    val letApp = tla.appOp(tla.name("t_3") ? "L") ? "i"
    val letBody =
      tla.exists(tla.name("t_1") ? "i", letApp,
          tla.exists(tla.name("t_2") ? "i", letApp,
              tla.not(tla.eql(tla.name("t_1") ? "i", tla.name("t_2") ? "i") ? "b") ? "b") ? "b")
    val decl = tla
      .declOp("t_3", tla.name("S").typed(types, "S"))
      .as(OperT1(Seq(), IntT1()))
    val expected =
      tla.letIn(letBody ? "b", decl).typed(types, "b")
    assert(expected == output)
  }

  test("""Cardinality(S) > 1 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_1 \in t_3: t_1 /= t_2""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1(), "L" -> OperT1(Seq(), IntT1()))
    val set = tla.name("S") ? "S"
    val input = tla
      .gt(tla.card(set) ? "i", tla.int(1))
      .typed(types, "b")
    val output = optimizer.apply(input)
    val letApp = tla.appOp(tla.name("t_3") ? "L") ? "i"
    val letBody =
      tla.exists(tla.name("t_1") ? "i", letApp,
          tla.exists(tla.name("t_2") ? "i", letApp,
              tla.not(tla.eql(tla.name("t_1") ? "i", tla.name("t_2") ? "i") ? "b") ? "b") ? "b")
    val decl = tla
      .declOp("t_3", tla.name("S").typed(types, "S"))
      .as(OperT1(Seq(), IntT1()))
    val expected =
      tla.letIn(letBody ? "b", decl).typed(types, "b")
    assert(expected == output)
  }

  test("""Cardinality(5..9) > 5""") {
    // regression #748
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .gt(tla.card(tla.dotdot(tla.int(5), tla.int(9)) ? "S") ? "i", tla.int(5))
      .typed(types, "b")
    // check that it does not throw an exception
    optimizer.apply(input)
  }

  test("""Cardinality(a..b) becomes (b - a) + 1""") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1())
    val input = tla
      .card(tla.dotdot(tla.name("a") ? "i", tla.name("b") ? "i") ? "S")
      .typed(types, "i")
    val output = optimizer.apply(input)
    val expected =
      tla
        .plus(tla.minus(tla.name("b") ? "i", tla.name("a") ? "i") ? "i", tla.int(1) ? "i")
        .typed(types, "i")
    assert(expected == output)
  }
}

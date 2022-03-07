package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, OperT1, RecT1, SetT1}
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite

@RunWith(classOf[JUnitRunner])
class TestExprOptimizer extends AnyFunSuite with BeforeAndAfterEach {
  private val intT = IntT1()
  private val boolT = BoolT1()
  private val intSetT = SetT1(IntT1())
  private val intSetSetT = SetT1(IntT1())
  private val boolSetT = SetT1(BoolT1())
  private var optimizer = new ExprOptimizer(new UniqueNameGenerator(), TrackerWithListeners())

  override def beforeEach(): Unit = {
    optimizer = new ExprOptimizer(new UniqueNameGenerator(), TrackerWithListeners())
  }

  // an optimization for integer ranges
  test("""e \in a..b ~~> e >= a /\ e <= b (but not if e is x')""") {
    val input =
      in(name("e").as(intT), dotdot(name("a").as(intT), name("b").as(intT)).as(intSetT)).as(boolT)
    val output = optimizer.apply(input)
    val expected =
      and(le(name("a").as(intT), name("e").as(intT)).as(boolT), le(name("e").as(intT), name("b").as(intT)).as(boolT))
        .as(boolT)
    assert(expected == output)
  }

  // an optimization for record accesses
  test("""[a |-> 1, b |-> 2].a becomes 2""") {
    val recT = RecT1("a" -> IntT1(), "b" -> IntT1())
    val record =
      enumFun(str("a"), int(1), str("b"), int(2))
    val input = appFun(record.as(recT), str("b")).as(intT)
    val output = optimizer.apply(input)
    val expected = int(2).typed()
    assert(expected == output)
  }

  // an optimization for set comprehensions (maps)
  test("""\E x \in {foo[y]: y \in {1, 2}}: z = x ~~> \E y \in {1, 2}: z = foo[y]""") {
    val funT = FunT1(IntT1(), BoolT1())
    val set12 = enumSet(int(1), int(2)).as(intSetT)
    val funApp = appFun(name("foo").as(funT), name("y").as(intT)).as(boolT)
    val mapEx = map(funApp, name("y").as(intT), set12).as(boolSetT)
    val input =
      exists(name("x").as(intSetT), mapEx, eql(name("z").as(intT), name("x").as(boolSetT)).as(boolT)).as(boolT)
    val output = optimizer.apply(input)
    val eq = eql(name("z").as(boolT), funApp).as(boolT)
    val expected =
      exists(name("y").as(intT), set12, eq).as(boolT)
    assert(expected == output)
  }

  // an optimization for set comprehensions (filters)
  test("""\E x \in {y \in {1, 2}: y = 1}: z = x ~~> \E y \in {1, 2}: z = y /\ y = 1""") {
    val set12 = enumSet(int(1), int(2)).as(intSetT)
    val filterEx =
      filter(name("y").as(intT), set12, eql(name("y").as(intT), int(1).as(intT)).as(boolT)).as(boolSetT)
    val input =
      exists(name("x").as(boolT), filterEx, eql(name("z").as(intT), name("x").as(boolT)).as(boolT)).as(boolT)
    val output = optimizer.apply(input)
    val y_eq_1 = eql(name("y").as(intT), int(1)).as(boolT)
    val z_eq_y = eql(name("z").as(intT), name("y").as(intT)).as(boolT)
    val expected =
      exists(name("y").as(intT), set12, and(y_eq_1, z_eq_y).as(boolT)).as(boolT)

    assert(expected == output)
  }

  // optimizations for set cardinalities

  test("""Cardinality(S) = 0 becomes S = {}""") {
    val input = eql(card(name("S").as(intSetT)).as(intT), int(0)).as(boolT)
    val output = optimizer.apply(input)
    val expected = eql(name("S").as(intSetT), enumSet().as(intSetT)).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(S) > 0 becomes ~(S = {})""") {
    val input = gt(card(name("S").as(intSetT)).as(intT), int(0)).as(boolT)
    val output = optimizer.apply(input)
    val expected =
      not(eql(name("S").as(intSetT), enumSet().as(intSetT)).as(boolT)).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(S) >= 1 becomes ~(S = {})""") {
    val input = ge(card(name("S").as(intSetT)).as(intT), int(1)).as(boolT)
    val output = optimizer.apply(input)
    val expected =
      not(eql(name("S").as(intSetT), enumSet().as(intSetT)).as(boolT)).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(S) /= 0 becomes ~(S = {})""") {
    val input = ge(card(name("S").as(intSetT)).as(intT), int(1)).as(boolT)
    val output = optimizer.apply(input)
    val expected =
      not(eql(name("S").as(intSetT), enumSet().as(intSetT)).as(boolT)).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(S) >= 2 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_2 \in t_3: t_1 /= t_2""") {
    val operT = OperT1(Seq(), IntT1())
    val set = name("S").as(intSetT)
    val input = ge(card(set).as(intT), int(2)).as(boolT)
    val output = optimizer.apply(input)
    val letApp = appOp(name("t_3").as(operT)).as(intT)
    val letBody =
      exists(name("t_1").as(intT), letApp,
          exists(name("t_2").as(intT), letApp, not(eql(name("t_1").as(intT), name("t_2").as(intT)).as(boolT)).as(boolT))
            .as(boolT))
    val decl = declOp("t_3", name("S").as(intSetT)).as(OperT1(Seq(), IntT1()))
    val expected = letIn(letBody.as(boolT), decl).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(S) > 1 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_1 \in t_3: t_1 /= t_2""") {
    val operT = OperT1(Seq(), IntT1())
    val set = name("S").as(intSetT)
    val input = gt(card(set).as(intT), int(1)).as(boolT)
    val output = optimizer.apply(input)
    val letApp = appOp(name("t_3").as(operT)).as(intT)
    val letBody =
      exists(name("t_1").as(intT), letApp,
          exists(name("t_2").as(intT), letApp, not(eql(name("t_1").as(intT), name("t_2").as(intT)).as(boolT)).as(boolT))
            .as(boolT))
    val decl = declOp("t_3", name("S").as(intSetT)).as(OperT1(Seq(), IntT1()))
    val expected =
      letIn(letBody.as(boolT), decl).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(5..9) > 5""") {
    // regression #748
    val input = gt(card(dotdot(int(5), int(9)).as(intSetT)).as(intT), int(5)).as(boolT)
    // check that it does not throw an exception
    optimizer.apply(input)
  }

  test("""Cardinality(a..b) becomes (b - a) + 1""") {
    val input = card(dotdot(name("a").as(intT), name("b").as(intT)).as(intSetT)).as(intT)
    val output = optimizer.apply(input)
    val expected =
      plus(minus(name("b").as(intT), name("a").as(intT)).as(intT), int(1).as(intT)).as(intT)
    assert(expected == output)
  }

  test("""Cardinality(SUBSET S) becomes 2^(Cardinality(S))""") {
    val input = card(powSet(name("S").as(intSetT)).as(intSetSetT)).as(intT)
    val output = optimizer.apply(input)
    val expected = exp(int(2), card(name("S").as(intSetT)).as(intT)).as(intT)
    assert(expected == output)
  }
}

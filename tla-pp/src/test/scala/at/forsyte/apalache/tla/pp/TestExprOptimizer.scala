package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
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
    val input = tla.in(tla.name("e"), tla.dotdot(tla.name("a"), tla.name("b")))
    val output = optimizer.apply(input)
    val expected =
      tla.and(
        tla.le(tla.name("a"), tla.name("e")),
        tla.le(tla.name("e"), tla.name("b"))
      ) ///
    assert(expected == output)
  }

  // an optimization for record accesses
  test("""[a |-> 1, b |-> 2].a becomes 2""") {
    val record = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.int(2))
    val input = tla.appFun(record, tla.str("b"))
    val output = optimizer.apply(input)
    val expected = tla.int(2)
    assert(expected == output)
  }

  // an optimization for set comprehensions (maps)
  test("""\E x \in {foo[y]: y \in {1, 2}}: z = x ~~> \E y \in {1, 2}: LET t_1 == foo[y] IN z = t_1""") {
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val map = tla.map(tla.appFun(tla.name("foo"), tla.name("y")),
      tla.name("y"),
      set12)
    val input =
      tla.exists(tla.name("x"), map, tla.eql(tla.name("z"), tla.name("x")))
    val output = optimizer.apply(input)
    val let = tla.letIn(
      tla.eql(tla.name("z"), tla.appOp(tla.name("t_1"))),
      TlaOperDecl("t_1", List(),
        tla.appFun(tla.name("foo"), tla.name("y")))
    ) //
    val expected = tla.exists(tla.name("y"), set12, let)
    assert(expected == output)
  }

  // an optimization for set comprehensions (filters)
  test("""\E x \in {y \in {1, 2}: y = 1}: z = x ~~> \E y \in {1, 2}: z = y /\ y = 1""") {
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val filter = tla.filter(
      tla.name("y"),
      set12,
      tla.eql(tla.name("y"), tla.int(1)))
    val input =
      tla.exists(tla.name("x"), filter, tla.eql(tla.name("z"), tla.name("x")))
    val output = optimizer.apply(input)
    val expected =
      tla.exists(
        tla.name("y"),
        set12,
        tla.and(tla.eql(tla.name("y"), tla.int(1)),
          tla.eql(tla.name("z"), tla.name("y"))))

    assert(expected == output)
  }

  // optimizations for set cardinalities

  test("""Cardinality(S) = 0 becomes \A t_1 \in S: FALSE""") {
    val input = tla.eql(tla.card(tla.name("S")), tla.int(0))
    val output = optimizer.apply(input)
    val expected = tla.forall(tla.name("t_1"), tla.name("S"), tla.bool(false))
    assert(expected == output)
  }

  test("""Cardinality(S) > 0 becomes \E t_1 \in S: TRUE""") {
    val input = tla.gt(tla.card(tla.name("S")), tla.int(0))
    val output = optimizer.apply(input)
    val expected = tla.exists(tla.name("t_1"), tla.name("S"), tla.bool(true))
    assert(expected == output)
  }

  test("""Cardinality(S) >= 1 becomes \E t_1 \in S: TRUE""") {
    val input = tla.ge(tla.card(tla.name("S")), tla.int(1))
    val output = optimizer.apply(input)
    val expected = tla.exists(tla.name("t_1"), tla.name("S"), tla.bool(true))
    assert(expected == output)
  }

  test("""Cardinality(S) /= 0 becomes \E t_1 \in S: TRUE""") {
    val input = tla.ge(tla.card(tla.name("S")), tla.int(1))
    val output = optimizer.apply(input)
    val expected = tla.exists(tla.name("t_1"), tla.name("S"), tla.bool(true))
    assert(expected == output)
  }

  test("""Cardinality(S) >= 2 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_1 \in t_3: t_1 /= t_2""") {
    val input = tla.ge(tla.card(tla.name("S")), tla.int(2))
    val output = optimizer.apply(input)
    val letBody =
      tla.exists(tla.name("t_1"), tla.name("t_3"),
        tla.exists(tla.name("t_2"), tla.name("t_3"),
          tla.not(tla.eql(tla.name("t_1"), tla.name("t_2")))))
    val expected = tla.letIn(letBody, TlaOperDecl("t_3", List(), tla.name("S")))
    assert(expected == output)
  }

  test("""Cardinality(S) > 1 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_1 \in t_3: t_1 /= t_2""") {
    val input = tla.gt(tla.card(tla.name("S")), tla.int(1))
    val output = optimizer.apply(input)
    val letBody =
      tla.exists(tla.name("t_1"), tla.name("t_3"),
        tla.exists(tla.name("t_2"), tla.name("t_3"),
          tla.not(tla.eql(tla.name("t_1"), tla.name("t_2")))))
    val expected = tla.letIn(letBody, TlaOperDecl("t_3", List(), tla.name("S")))
    assert(expected == output)
  }
}
package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, OperEx, OperT1, RecT1, SetT1, StrT1, TupT1, Typed}
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}

@RunWith(classOf[JUnitRunner])
class TestExprOptimizer extends AnyFunSuite with BeforeAndAfterEach {
  private val intT = IntT1
  private val boolT = BoolT1
  private val intSetT = SetT1(IntT1)
  private val intSetSetT = SetT1(IntT1)
  private val boolSetT = SetT1(BoolT1)
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

  // an optimization for x \in { y \in S: P }
  test("""x \in { y \in 1..3: y > 2 }""") {
    val set123 = enumSet(int(1), int(2), int(3)).as(intSetT)
    val filteredSet = filter(name("y").as(intT), set123, gt(name("y").as(intT), int(2)).as(boolT)).as(intSetT)
    val input = in(name("x").as(intT), filteredSet).as(boolT)
    val output = optimizer.apply(input)
    val expected = and(in(name("x").as(intT), set123).as(boolT), gt(name("x").as(intT), int(2)).as(boolT)).as(boolT)
    assert(expected == output)
  }

  // an optimization for record accesses
  test("""[a |-> 1, b |-> 2].a becomes 2""") {
    val recT = RecT1("a" -> IntT1, "b" -> IntT1)
    val record =
      enumFun(str("a"), int(1), str("b"), int(2))
    val input = appFun(record.as(recT), str("b")).as(intT)
    val output = optimizer.apply(input)
    val expected = int(2).typed()
    assert(expected == output)
  }

  // an optimization for set comprehensions (maps)
  test("""\E x \in {foo[y]: y \in {1, 2}}: z = x ~~> \E y \in {1, 2}: z = foo[y]""") {
    val funT = FunT1(IntT1, BoolT1)
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

  // An optimization for set membership over sets of records. Note that this is the standard form produced by Keramelizer.
  test("""r \in { [a |-> x, b |-> y]: x \in S, y \in T } becomes DOMAIN r = { "a", "b" } /\ r.a \in S /\ r.b \in T""") {
    // ... [a |-> x, b |-> y] ...
    val recT = RecT1("a" -> IntT1, "b" -> IntT1)
    // ... x \in S, y \in T ...
    val record =
      enumFun(str("a"), name("x").as(intT), str("b"), name("y").as(intT)).as(recT)
    // ... S ...
    val S = name("S").as(intSetT)
    // ... T ...
    val T = name("T").as(intSetT)
    // { ... }
    val recSetT = SetT1(recT)
    val recordSet = map(record, name("x").as(intT), S, name("y").as(intT), T).as(recSetT)
    // r ...
    val r = name("r").as(recT)
    // ... \in ...
    val input = in(r, recordSet).as(boolT)

    // ~~>

    // DOMAIN r = { "a", "b" }
    val strSetT = SetT1(StrT1)
    val domEq = eql(dom(r).as(strSetT), enumSet(str("a"), str("b")).as(strSetT)).as(boolT)
    // r.a \in S
    val memA = in(appFun(r, str("a")).as(intT), S).as(boolT)
    // r.b \in T
    val memB = in(appFun(r, str("b")).as(intT), T).as(boolT)
    // ... /\ ... /\ ...
    val expected = and(domEq, memA, memB).as(boolT)
    val output = optimizer.apply(input)

    assert(expected == output)
  }

  // An optimization for set membership of the powerset of a record where the record has infinite co-domains.
  test("""S \in SUBSET [a : T] ~~> \A r \in S: DOMAIN r = { "a" } /\ r.a \in T""") {

    // ... { [a |-> x] : x \in T } ...
    val recT = RecT1("a" -> IntT1)
    val record =
      enumFun(str("a"), name("x").as(intT)).as(recT)
    val T = name("T").as(intSetT)
    val recSetT = SetT1(recT)
    val recordSet = map(record, name("x").as(intT), T).as(recSetT)

    // ... SUBSET ...
    val powSetT = powSet(recordSet).as(recSetT)

    // S ...
    val s = name("S").as(recSetT)

    // ... \in ...
    val input = in(s, powSetT).as(boolT)
    val output = optimizer.apply(input)

    // ~~>

    // DOMAIN r = { "a" }
    val r = name("t_1").as(recT)
    val strSetT = SetT1(StrT1)
    val domEq = eql(dom(r).as(strSetT), enumSet(str("a")).as(strSetT)).as(boolT)

    // r.a \in T
    val memA = in(appFun(r, str("a")).as(intT), T).as(boolT)

    // ... /\ ...
    val conjunct = and(domEq, memA).as(boolT)

    // \A ...
    val expected = forall(r, s, conjunct).as(boolT)

    assert(expected == output)
  }

  test("""S \in SUBSET [a : T, b : U] ~~> \A r \in S: DOMAIN r = { "a", "b" } /\ r.a \in T /\ r.b \in U""") {
    val recT = RecT1("a" -> IntT1, "b" -> IntT1)
    val record =
      enumFun(str("a"), name("x").as(intT), str("b"), name("y").as(intT)).as(recT)
    val T = name("T").as(intSetT)
    val U = name("U").as(intSetT)
    val recSetT = SetT1(recT)
    val recordSet = map(record, name("x").as(intT), T, name("y").as(intT), U).as(recSetT)
    val powSetT = powSet(recordSet).as(recSetT)
    val s = name("S").as(recSetT)
    val input = in(s, powSetT).as(boolT)
    val output = optimizer.apply(input)

    val r = name("t_1").as(recT)
    val strSetT = SetT1(StrT1)
    val domEq = eql(dom(r).as(strSetT), enumSet(str("a"), str("b")).as(strSetT)).as(boolT)
    val memA = in(appFun(r, str("a")).as(intT), T).as(boolT)
    val memB = in(appFun(r, str("b")).as(intT), U).as(boolT)
    val conjunct = and(domEq, memA, memB).as(boolT)
    val expected = forall(r, s, conjunct).as(boolT)

    assert(expected == output)
  }

  test("""S \in SUBSET T ~~> \A s \in S: s \in T""") {
    val T = name("T").as(intSetT)
    val S = name("S").as(intSetT)
    val powSetT = powSet(T).as(intSetT)
    val input = in(S, powSetT).as(boolT)
    val output = optimizer.apply(input)

    val s = name("t_1").as(intT)
    val expected = forall(s, S, in(s, T).as(boolT)).as(boolT)

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
    val operT = OperT1(Seq(), IntT1)
    val set = name("S").as(intSetT)
    val input = ge(card(set).as(intT), int(2)).as(boolT)
    val output = optimizer.apply(input)
    val letApp = appOp(name("t_3").as(operT)).as(intT)
    val letBody =
      exists(name("t_1").as(intT), letApp,
          exists(name("t_2").as(intT), letApp, not(eql(name("t_1").as(intT), name("t_2").as(intT)).as(boolT)).as(boolT))
            .as(boolT))
    val decl = declOp("t_3", name("S").as(intSetT)).as(OperT1(Seq(), IntT1))
    val expected = letIn(letBody.as(boolT), decl).as(boolT)
    assert(expected == output)
  }

  test("""Cardinality(S) > 1 becomes LET t_3 == S IN \E t_1 \in t_3: \E t_1 \in t_3: t_1 /= t_2""") {
    val operT = OperT1(Seq(), IntT1)
    val set = name("S").as(intSetT)
    val input = gt(card(set).as(intT), int(1)).as(boolT)
    val output = optimizer.apply(input)
    val letApp = appOp(name("t_3").as(operT)).as(intT)
    val letBody =
      exists(name("t_1").as(intT), letApp,
          exists(name("t_2").as(intT), letApp, not(eql(name("t_1").as(intT), name("t_2").as(intT)).as(boolT)).as(boolT))
            .as(boolT))
    val decl = declOp("t_3", name("S").as(intSetT)).as(OperT1(Seq(), IntT1))
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

  test("""Cardinality(a..b) becomes IF a =< b THEN (b - a) + 1 ELSE 0""") {
    val input = card(dotdot(name("a").as(intT), name("b").as(intT)).as(intSetT)).as(intT)
    val output = optimizer.apply(input)
    val expected =
      ite(
          le(name("a").as(intT), name("b").as(intT)).as(boolT),
          plus(minus(name("b").as(intT), name("a").as(intT)).as(intT), int(1)).as(intT),
          int(0),
      ).as(intT)
    assert(expected == output)
  }

  test("""Cardinality(SUBSET S) becomes 2^(Cardinality(S))""") {
    val input = card(powSet(name("S").as(intSetT)).as(intSetSetT)).as(intT)
    val output = optimizer.apply(input)
    val expected = exp(int(2), card(name("S").as(intSetT)).as(intT)).as(intT)
    assert(expected == output)
  }

  // an optimization for set membership over sets of tuples.
  test("""t \in { <<x, y>>: x \in S, y \in T } becomes t[1] \in S /\ t[2] \in T""") {
    val tupT = TupT1(IntT1, BoolT1)
    val tuple_xy = tuple(name("x").as(intT), name("y").as(boolT)).as(tupT)
    val S = name("S").as(intSetT)
    val T = name("T").as(boolSetT)
    val tupleSet = map(tuple_xy, name("x").as(intT), S, name("y").as(boolT), T).as(SetT1(tupT))
    val t = name("t").as(tupT)
    val input = in(t, tupleSet).as(boolT)

    val mem1 = in(appFun(t, int(1)).as(intT), S).as(boolT)
    val mem2 = in(appFun(t, int(2)).as(boolT), T).as(boolT)
    val expected = and(mem1, mem2).as(boolT)
    val output = optimizer.apply(input)

    assert(expected == output)
    output match {
      case OperEx(TlaBoolOper.and, OperEx(TlaSetOper.in, t1, _), OperEx(TlaSetOper.in, t2, _)) =>
        assert(t1.typeTag == Typed(intT))
        assert(t2.typeTag == Typed(boolT))

      case _ =>
        fail(s"Unexpected output: $output")
    }
  }

  test("""t \in (A \X B) \X C becomes t[1][1] \in A /\ t[1][2] \in B /\ t[2] \in C""") {
    val abT = TupT1(IntT1, IntT1)
    val tupT = TupT1(abT, IntT1)
    val A = name("A").as(intSetT)
    val B = name("B").as(intSetT)
    val C = name("C").as(intSetT)
    val tuple_ab = tuple(name("a").as(intT), name("b").as(intT)).as(abT)
    val setAB = map(tuple_ab, name("a").as(intT), A, name("b").as(intT), B).as(SetT1(abT))
    val tuple_xy = tuple(name("x").as(abT), name("y").as(intT)).as(tupT)
    val tupleSet = map(tuple_xy, name("x").as(abT), setAB, name("y").as(intT), C).as(SetT1(tupT))
    val t = name("t").as(tupT)
    val input = in(t, tupleSet).as(boolT)
    val output = optimizer.apply(input)

    val t1 = appFun(t, int(1)).as(abT)
    val memAB = and(in(appFun(t1, int(1)).as(intT), A).as(boolT), in(appFun(t1, int(2)).as(intT), B).as(boolT))
      .as(boolT)
    val memC = in(appFun(t, int(2)).as(intT), C).as(boolT)
    val expected = and(memAB, memC).as(boolT)

    assert(expected == output)
  }

  test("""t \in { <<y, x>>: x \in S, y \in T } is not optimized""") {
    val tupT = TupT1(IntT1, IntT1)
    val tuple_yx = tuple(name("y").as(intT), name("x").as(intT)).as(tupT)
    val S = name("S").as(intSetT)
    val T = name("T").as(intSetT)
    val tupleSet = map(tuple_yx, name("x").as(intT), S, name("y").as(intT), T).as(SetT1(tupT))
    val input = in(name("t").as(tupT), tupleSet).as(boolT)
    val output = optimizer.apply(input)

    assert(input == output)
  }

}

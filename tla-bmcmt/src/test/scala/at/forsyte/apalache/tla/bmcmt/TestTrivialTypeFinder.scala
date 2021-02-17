package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaStrSet}
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.SortedMap

// TODO: add tests for TlaSetOper.seqSet

@RunWith(classOf[JUnitRunner])
class TestTrivialTypeFinder extends RewriterBase {
  test("compute IntT") {
    val typeFinder = new TrivialTypeFinder()
    val cellType = typeFinder.compute(tla.int(1))
    assert(IntT() == cellType)
  }

  test("compute BoolT") {
    val typeFinder = new TrivialTypeFinder()
    val cellType = typeFinder.compute(tla.bool(false))
    assert(BoolT() == cellType)
  }

  test("compute ConstT") {
    val typeFinder = new TrivialTypeFinder()
    val cellType = typeFinder.compute(tla.str("hello"))
    assert(ConstT() == cellType)
  }

  test("compute names") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    typeFinder.reset(Map("x" -> BoolT()))
    assert(BoolT() == typeFinder.compute(x))
    typeFinder.reset(Map.empty)
    typeFinder.compute(x)
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute basic operators") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val p = tla.name("p")
    val set1 = tla.name("S")
    val set2 = tla.name("T")
    // good cases
    assert(
        BoolT() ==
          typeFinder.compute(tla.eql(set1, set2), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        BoolT() ==
          typeFinder.compute(tla.neql(set1, set2), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        IntT() ==
          typeFinder.compute(tla.choose(x, set1, p), IntT(), FinSetT(IntT()), BoolT()))
    assert(
        IntT() ==
          typeFinder.compute(tla.choose(x, p), IntT(), BoolT()))
    assert(
        IntT() ==
          typeFinder.compute(OperEx(TlaOper.chooseIdiom, set1), FinSetT(IntT())))
    assert(
        FinSetT(IntT())
          == typeFinder.compute(tla.label(set1, "lab", "a"), FinSetT(IntT()), ConstT(), ConstT()))
    // bad cases
    typeFinder.compute(tla.eql(set1, set2), FinSetT(IntT()), FinSetT(BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)

    typeFinder.compute(tla.neql(set1, set2), FinSetT(IntT()), FinSetT(BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)
    assert(
        IntT() ==
          typeFinder.compute(tla.choose(x, set1, p), BoolT(), FinSetT(IntT()), BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.choose(x, set1, p), IntT(), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    assert(
        IntT() ==
          typeFinder.compute(tla.choose(x, set1, p), IntT(), FinSetT(IntT()), IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    assert(IntT() == typeFinder.compute(tla.choose(x, p), IntT(), IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(OperEx(TlaOper.chooseIdiom, set1), IntT())
    assert(typeFinder.typeErrors.nonEmpty)

    typeFinder.compute(tla.label(set1, "lab", "a"), FinSetT(IntT()), IntT(), ConstT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute int to int operators") {
    val typeFinder = new TrivialTypeFinder()
    val i = tla.name("i")
    val j = tla.name("j")
    // good cases
    assert(IntT() == typeFinder.compute(tla.uminus(i), IntT()))
    assert(IntT() == typeFinder.compute(tla.plus(i, j), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.minus(i, j), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.mult(i, j), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.div(i, j), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.mod(i, j), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.exp(i, j), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.sum(i, i, j), IntT(), IntT(), IntT()))
    assert(IntT() == typeFinder.compute(tla.prod(i, i, j), IntT(), IntT(), IntT()))
    // bad cases
    typeFinder.compute(tla.uminus(i), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.plus(i, j), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.minus(i, j), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.mult(i, j), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.div(i, j), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.mod(i, j), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.exp(i, j), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.sum(i, i, j), IntT(), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute int to bool operators") {
    val typeFinder = new TrivialTypeFinder()
    val i = tla.name("i")
    val j = tla.name("j")
    // good cases
    assert(BoolT() == typeFinder.compute(tla.lt(i, j), IntT(), IntT()))
    assert(BoolT() == typeFinder.compute(tla.gt(i, j), IntT(), IntT()))
    assert(BoolT() == typeFinder.compute(tla.le(i, j), IntT(), IntT()))
    assert(BoolT() == typeFinder.compute(tla.ge(i, j), IntT(), IntT()))
    // bad cases
    typeFinder.compute(tla.lt(i, j), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.gt(i, j), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.le(i, j), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.ge(i, j), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute int to X operators") {
    val typeFinder = new TrivialTypeFinder()
    val i = tla.name("i")
    val j = tla.name("j")
    // good cases
    assert(FinSetT(IntT()) == typeFinder.compute(tla.dotdot(i, j), IntT(), IntT()))
    // bad cases
    typeFinder.compute(tla.dotdot(i, j), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute bool operators") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val p = tla.name("p")
    val q = tla.name("q")
    val S = tla.name("S")
    // good cases
    assert(BoolT() == typeFinder.compute(tla.not(p), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.and(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.or(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.impl(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.equiv(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.forall(x, S, p), IntT(), FinSetT(IntT()), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.exists(x, S, p), IntT(), FinSetT(IntT()), BoolT()))
    // bad cases
    typeFinder.compute(tla.not(p), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.and(p, q), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.or(p, q), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.impl(p, q), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.equiv(p, q), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.forall(x, S, p), IntT(), FinSetT(ConstT()), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.exists(x, S, p), IntT(), FinSetT(ConstT()), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute control operators") {
    val typeFinder = new TrivialTypeFinder()
    val p = NameEx("p")
    val q = NameEx("q")
    val x = NameEx("x")
    val y = NameEx("y")
    val z = NameEx("z")
    // good cases
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.ite(p, x, y), BoolT(), FinSetT(IntT()), FinSetT(IntT())))
    val caseEx = tla.caseSplit(p, x, q, y)
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(caseEx, BoolT(), FinSetT(IntT()), BoolT(), FinSetT(IntT())))
    val caseOtherEx = tla.caseOther(z, p, x, q, y)
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(caseOtherEx, FinSetT(IntT()), BoolT(), FinSetT(IntT()), BoolT(), FinSetT(IntT())))

    val decl = TlaOperDecl("A", List(), tla.plus(tla.int(1), tla.int(2)))
    val letIn = tla.letIn(tla.plus(tla.int(1), tla.appDecl(decl)), decl)
    assert(IntT() == typeFinder.compute(letIn, IntT()))
    // bad cases
    typeFinder.compute(tla.ite(p, x, y), IntT(), FinSetT(IntT()), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.ite(p, x, y), BoolT(), FinSetT(BoolT()), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(caseEx, BoolT(), FinSetT(IntT()), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(caseEx, BoolT(), FinSetT(IntT()), BoolT(), FinSetT(BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(caseOtherEx, FinSetT(BoolT()), BoolT(), FinSetT(IntT()), BoolT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(caseOtherEx, FinSetT(IntT()), BoolT(), FinSetT(IntT()), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute Boolean set operators") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // good cases
    assert(
        BoolT() ==
          typeFinder.compute(tla.in(int1, set12), IntT(), FinSetT(IntT())))
    assert(
        BoolT() ==
          typeFinder.compute(tla.notin(int1, set12), IntT(), FinSetT(IntT())))
    assert(
        BoolT() ==
          typeFinder.compute(tla.subset(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        BoolT() ==
          typeFinder.compute(tla.subseteq(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        BoolT() ==
          typeFinder.compute(tla.supset(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        BoolT() ==
          typeFinder.compute(tla.supseteq(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    // bad cases
    typeFinder.compute(tla.in(set12, set12), FinSetT(IntT()), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.notin(set12, set12), FinSetT(IntT()), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.subset(int1, set12), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.subseteq(int1, set12), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.supset(int1, set12), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.supseteq(int1, set12), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute set ctor") {
    val typeFinder = new TrivialTypeFinder()
    val cellType = typeFinder.compute(tla.enumSet(tla.int(1)), IntT())
    assert(FinSetT(IntT()) == cellType)
  }

  test("compute set-algebraic operators") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // good cases
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.cup(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.cap(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.setminus(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    // bad cases
    typeFinder.compute(tla.cup(int1, set123), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.cap(int1, set123), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.setminus(int1, set123), IntT(), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute set filter") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    // good cases
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.filter(NameEx("x"), set12, tla.bool(true)), IntT(), FinSetT(IntT()), BoolT()))
    // bad cases
    typeFinder.compute(tla.filter(NameEx("x"), int1, tla.bool(true)), IntT(), IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.filter(NameEx("x"), set12, int1), IntT(), FinSetT(IntT()), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute set map") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    // good cases
    assert(
        FinSetT(BoolT()) ==
          typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), set12), BoolT(), IntT(), FinSetT(IntT())))
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), set12), IntT(), BoolT(), FinSetT(BoolT())))
    // bad cases
    typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), int1), BoolT(), IntT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), set12, NameEx("y"), int1), BoolT(), IntT(), FinSetT(IntT()),
        IntT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute UNION") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set3 = tla.enumSet(tla.int(3))
    // good cases
    assert(
        FinSetT(IntT()) ==
          typeFinder.compute(tla.union(tla.enumSet(set12, set3)), FinSetT(FinSetT(IntT()))))
    // bad cases
    typeFinder.compute(tla.union(set12), FinSetT(IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute SUBSET") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set3 = tla.enumSet(tla.int(3))

    // good cases
    assert(
        FinSetT(FinSetT(IntT())) ==
          typeFinder.compute(tla.powSet(set12), FinSetT(IntT())))
    // bad cases
    typeFinder.compute(tla.powSet(int1), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute \\X") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set3 = tla.enumSet(tla.bool(true))

    // good cases
    assert(FinSetT(TupleT(Seq(IntT(), BoolT()))) ==
          typeFinder.compute(tla.times(set12, set3), FinSetT(IntT()), FinSetT(BoolT())))
    // bad cases
    typeFinder.compute(tla.times(set12, int1), FinSetT(IntT()), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute [S -> T]") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val boolSet = tla.enumSet(tla.bool(false), tla.bool(true))

    // good cases
    assert(FinSetT(FunT(FinSetT(IntT()), BoolT())) ==
          typeFinder.compute(tla.funSet(set12, boolSet), FinSetT(IntT()), FinSetT(BoolT())))
    // bad cases
    typeFinder.compute(tla.funSet(set12, tla.bool(false)), FinSetT(IntT()), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.funSet(int1, boolSet), IntT(), FinSetT(BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute [a: S, b: T]") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val boolSet = tla.enumSet(tla.bool(false), tla.bool(true))

    // good cases
    assert(FinSetT(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT()))) ==
          typeFinder.compute(tla.recSet(tla.str("a"), set12, tla.str("b"), boolSet), ConstT(), FinSetT(IntT()),
              ConstT(), FinSetT(BoolT())))
    // bad cases
    typeFinder.compute(tla.recSet(tla.str("a"), int1, tla.str("b"), boolSet), ConstT(), IntT(), ConstT(),
        FinSetT(BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute [a |-> 1, b |-> FALSE]") {
    val typeFinder = new TrivialTypeFinder()
    val rec = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))
    val cellType = typeFinder.compute(rec, ConstT(), IntT(), ConstT(), BoolT())
    assert(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT())) == cellType)
    typeFinder.compute(rec, IntT(), IntT(), ConstT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute <<1, FALSE>>") {
    val typeFinder = new TrivialTypeFinder()
    val tup = tla.tuple(tla.int(1), tla.bool(false))
    val cellType = typeFinder.compute(tup, IntT(), BoolT())
    assert(TupleT(Seq(IntT(), BoolT())) == cellType)
    // an empty tuple is a sequence, but its type is unknown
    assert(SeqT(UnknownT()) == typeFinder.compute(tla.tuple()))
  }

  test("compute <<1, FALSE>>[1]") {
    val typeFinder = new TrivialTypeFinder()
    val tup = tla.tuple(tla.int(1), tla.bool(false))
    val tupleType = TupleT(Seq(IntT(), BoolT()))
    assert(
        IntT() ==
          typeFinder.compute(tla.appFun(tup, tla.int(1)), tupleType, IntT()))
    assert(
        BoolT() ==
          typeFinder.compute(tla.appFun(tup, tla.int(2)), tupleType, IntT()))
    // out-of-range expressions
    typeFinder.compute(tla.appFun(tup, tla.int(0)), tupleType, IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.appFun(tup, tla.int(3)), tupleType, IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    // only integer constants are allowed!
    typeFinder.compute(tla.appFun(tup, tla.name("j")), tupleType, IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute r.a") {
    val typeFinder = new TrivialTypeFinder()
    val rec = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))
    val recType = RecordT(SortedMap("a" -> IntT(), "b" -> BoolT()))

    assert(
        IntT() ==
          typeFinder.compute(tla.appFun(rec, tla.str("a")), recType, ConstT()))
    assert(
        BoolT() ==
          typeFinder.compute(tla.appFun(rec, tla.str("b")), recType, ConstT()))
    // out-of-range expressions
    typeFinder.compute(tla.appFun(rec, tla.str("c")), recType, ConstT())
    assert(typeFinder.typeErrors.nonEmpty)
    // only string constants are allowed!
    typeFinder.compute(tla.appFun(rec, tla.name("x")), recType, ConstT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute f[x]") {
    val typeFinder = new TrivialTypeFinder()
    val fun = tla.name("f") // we know just the name
    val funType = FunT(FinSetT(IntT()), BoolT())

    assert(
        BoolT() ==
          typeFinder.compute(tla.appFun(fun, tla.int(1)), funType, IntT()))
    // wrong argument type
    typeFinder.compute(tla.appFun(fun, tla.str("c")), funType, ConstT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute DOMAIN fun") {
    val typeFinder = new TrivialTypeFinder()
    val fun = tla.name("f") // we know just the name
    val funType = FunT(FinSetT(BoolT()), BoolT())

    assert(FinSetT(BoolT()) == typeFinder.compute(tla.dom(fun), funType))
    // wrong argument type
    typeFinder.compute(tla.dom(fun), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute DOMAIN rec") {
    val typeFinder = new TrivialTypeFinder()
    val rec = tla.name("r") // we know just the name
    val recType = RecordT(SortedMap("a" -> IntT(), "b" -> BoolT()))

    assert(FinSetT(ConstT()) == typeFinder.compute(tla.dom(rec), recType))
    // wrong argument type
    typeFinder.compute(tla.dom(rec), ConstT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute DOMAIN tuple") {
    val typeFinder = new TrivialTypeFinder()
    val tup = tla.name("t") // we know just the name
    val tupType = TupleT(Seq(IntT(), BoolT()))

    assert(FinSetT(IntT()) == typeFinder.compute(tla.dom(tup), tupType))
    // wrong argument type
    typeFinder.compute(tla.dom(tup), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute [x \\in S |-> e]") {
    val typeFinder = new TrivialTypeFinder()
    val S = tla.name("S")
    val x = tla.name("x")
    val T = tla.name("T")
    val y = tla.name("y")
    val e = tla.name("e")
    // good cases
    assert(FunT(FinSetT(IntT()), BoolT()) ==
          typeFinder.compute(tla.funDef(e, x, S), BoolT(), IntT(), FinSetT(IntT())))
    assert(FunT(FinSetT(TupleT(Seq(IntT(), ConstT()))), BoolT()) ==
          typeFinder.compute(tla.funDef(e, x, S, y, T), BoolT(), IntT(), FinSetT(IntT()), ConstT(), FinSetT(ConstT())))
    // bad cases
    assertThrows[TypeException] {
      typeFinder.compute(tla.funDef(e, x, S), BoolT(), ConstT(), IntT())
    }
  }

  test("compute [f EXCEPT ![e] = g]") {
    val typeFinder = new TrivialTypeFinder()
    val f = tla.name("f")
    val e = tla.name("e")
    val g = tla.name("g")
    // good cases
    val funT = FunT(FinSetT(IntT()), BoolT())
    // TlaFunOper.except expects an index (single-dimensional as well as multi-dimensional) wrapped into a tuple
    assert(
        funT ==
          typeFinder.compute(tla.except(f, e, g), funT, TupleT(Seq(IntT())), BoolT()))
    val fun2T = FunT(FinSetT(TupleT(Seq(IntT(), ConstT()))), BoolT())
    assert(
        fun2T ==
          typeFinder.compute(tla.except(f, e, g), fun2T, TupleT(Seq(TupleT(Seq(IntT(), ConstT())))), BoolT()))
    // bad cases
    typeFinder.compute(tla.except(f, e, g), funT, IntT(), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    // the type of the new value must agree with the function result
    typeFinder.compute(tla.except(f, e, g), funT, TupleT(Seq(IntT())), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute FiniteSet operators") {
    val typeFinder = new TrivialTypeFinder()
    val S = tla.name("S")
    // good cases
    assert(BoolT() == typeFinder.compute(tla.isFin(S), FinSetT(IntT())))
    assert(IntT() == typeFinder.compute(tla.card(S), FinSetT(IntT())))
    // bad cases
    typeFinder.compute(tla.isFin(S), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.card(S), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute Sequences operators") {
    val typeFinder = new TrivialTypeFinder()
    val seq = tla.name("seq")
    val x = tla.name("x")
    // good cases
    assert(IntT() == typeFinder.compute(tla.head(seq), SeqT(IntT())))
    assert(SeqT(IntT()) == typeFinder.compute(tla.tail(seq), SeqT(IntT())))
    assert(SeqT(IntT()) == typeFinder.compute(tla.append(seq, x), SeqT(IntT()), IntT()))
    assert(SeqT(IntT()) == typeFinder.compute(tla.concat(seq, seq), SeqT(IntT()), SeqT(IntT())))
    assert(IntT() == typeFinder.compute(tla.len(seq), SeqT(IntT())))
    assert(SeqT(BoolT()) == typeFinder.compute(tla.subseq(seq, x, x), SeqT(BoolT()), IntT(), IntT()))
    // bad cases
    typeFinder.compute(tla.head(seq), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.tail(seq), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.append(seq, x), SeqT(IntT()), BoolT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.append(seq, x), IntT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.append(seq, x), TupleT(Seq(IntT())), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.concat(seq, seq), SeqT(IntT()), SeqT(BoolT()))
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.len(seq), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    typeFinder.compute(tla.subseq(seq, x, x), SeqT(BoolT()), BoolT(), IntT())
    assert(typeFinder.typeErrors.nonEmpty)
    assertThrows[NotImplementedError] {
      typeFinder.compute(tla.selectseq(seq, x), SeqT(IntT()), BoolT())
    }
  }

  test("compute TLC operators") {
    val typeFinder = new TrivialTypeFinder()
    val e = tla.name("e")
    val msg = "message"
    // good cases:
    // We only allow assert to return a Boolean result.
    // When you use assert in a non-Boolean expression, provide the tool with a type annotation.
    assert(BoolT() == typeFinder.compute(tla.tlcAssert(e, msg), BoolT(), ConstT()))
    // bad cases
    assert(BoolT() == typeFinder.compute(tla.tlcAssert(e, msg), IntT(), ConstT()))
    assert(typeFinder.typeErrors.nonEmpty)
    assert(BoolT() == typeFinder.compute(tla.tlcAssert(e, msg), BoolT(), IntT()))
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("compute labels") {
    val typeFinder = new TrivialTypeFinder()
    val e = tla.name("e")
    val msg = "message"
    // good cases:
    // We only allow assert to return a Boolean result.
    // When you use assert in a non-Boolean expression, provide the tool with a type annotation.
    assert(IntT() == typeFinder.compute(tla.label(tla.int(1), "lab", "a"), IntT(), ConstT(), ConstT()))
    assert(BoolT() == typeFinder.compute(tla.label(tla.bool(false), "lab", "a"), BoolT(), ConstT(), ConstT()))
    // no bad cases, as it is impossible to construct an ill-typed label
  }

  test("inferAndSave variable assignment") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val assign = tla.assignPrime(x, tla.int(1))
    assert(typeFinder.inferAndSave(assign).contains(BoolT()))
    assert(IntT() == typeFinder.varTypes("x'"))
  }

  test("inferAndSave double assignment") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    // double assignment is fine as soon as the types are preserved
    val assign =
      tla.or(
          tla.assignPrime(x, tla.int(1)),
          tla.assignPrime(x, tla.int(3))
      )
    assert(typeFinder.inferAndSave(assign).contains(BoolT()))
    assert(IntT() == typeFinder.varTypes("x'"))
  }

  test("inferAndSave set filter") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val filter = tla.filter(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(filter).contains(FinSetT(IntT())))
    assert(IntT() == typeFinder.varTypes("x"))
  }

  test("inferAndSave set map") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    val map = tla.map(tla.enumSet(x), x, tla.enumSet(tla.int(3)))
    assert(typeFinder.inferAndSave(map).contains(FinSetT(FinSetT(IntT()))))
    assert(IntT() == typeFinder.varTypes("x"))
  }

  test("inferAndSave exists/forall") {
    var typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val exists = tla.exists(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(exists).contains(BoolT()))
    assert(IntT() == typeFinder.varTypes("x"))
    typeFinder = new TrivialTypeFinder()
    val forall = tla.exists(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(forall).contains(BoolT()))
    assert(IntT() == typeFinder.varTypes("x"))
    // bad cases
    typeFinder = new TrivialTypeFinder()
    assert(typeFinder.inferAndSave(tla.exists(x, tla.enumSet(tla.int(3)), tla.int(4))).isEmpty)
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("inferAndSave CHOOSE") {
    var typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val choose = tla.choose(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(choose).contains(IntT()))
    assert(IntT() == typeFinder.varTypes("x"))
    // bad cases
    typeFinder = new TrivialTypeFinder()
    val badChoose = tla.choose(x, tla.enumSet(tla.int(3)), tla.int(4))
    assert(typeFinder.inferAndSave(badChoose).isEmpty)
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("inferAndSave [x \\in S |-> e]") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val map = tla.funDef(tla.enumSet(x), x, tla.enumSet(tla.int(1)))
    assert(typeFinder.inferAndSave(map).contains(FunT(FinSetT(IntT()), FinSetT(IntT()))))
    assert(IntT() == typeFinder.varTypes("x"))
  }

  test("inferAndSave [x \\in S, y \\in T |-> e]") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    val map = tla.funDef(tla.enumSet(x), x, tla.enumSet(tla.int(1)), y, tla.enumSet(tla.bool(false)))
    assert(typeFinder.inferAndSave(map).contains(FunT(FinSetT(TupleT(Seq(IntT(), BoolT()))), FinSetT(IntT()))))
    assert(IntT() == typeFinder.varTypes("x"))
    assert(BoolT() == typeFinder.varTypes("y"))
  }

  test("inferAndSave LET A == 1 + 2 IN 1 + A") {
    val typeFinder = new TrivialTypeFinder()
    val decl = TlaOperDecl("A", List(), tla.plus(tla.int(1), tla.int(2)))
    val letIn = tla.letIn(tla.plus(tla.int(1), tla.appDecl(decl)), decl)
    assert(typeFinder.inferAndSave(letIn).contains(IntT()))
    assert(IntT() == typeFinder.varTypes("A"))
  }

  test("inferAndSave recFunRef w/o annotation") {
    val typeFinder = new TrivialTypeFinder()
    val recFunRef = tla.recFunRef()
    typeFinder.inferAndSave(recFunRef)
    assert(typeFinder.typeErrors.nonEmpty)
  }

  test("inferAndSave recFunRef with annotation") {
    val typeFinder = new TrivialTypeFinder()
    val recFunRef = tla.withType(tla.recFunRef(), tla.funSet(ValEx(TlaIntSet), ValEx(TlaIntSet)))
    val tp = typeFinder.inferAndSave(recFunRef)
    assert(typeFinder.typeErrors.isEmpty)
    assert(tp.contains(FunT(FinSetT(IntT()), IntT())))
  }

  test("inferAndSave recFunDef with annotation") {
    val typeFinder = new TrivialTypeFinder()
    val recFunRef = tla.withType(tla.recFunRef(), tla.funSet(ValEx(TlaIntSet), ValEx(TlaIntSet)))
    val recFunApply = tla.appFun(recFunRef, NameEx("x"))
    // f[x \in {1, 2}] == f[x]
    val recFun = tla.recFunDef(recFunApply, NameEx("x"), tla.enumSet(tla.int(1), tla.int(2)))
    val tp = typeFinder.inferAndSave(recFun)
    assert(typeFinder.typeErrors.isEmpty)
    assert(tp.contains(FunT(FinSetT(IntT()), IntT())))
  }

  test("inferAndSave type annotation") {
    val typeFinder = new TrivialTypeFinder()
    val ex = tla.enumSet()

    val annotatedEx = tla.withType(ex, tla.enumSet(ValEx(TlaIntSet)))
    assert(typeFinder.inferAndSave(annotatedEx).contains(FinSetT(IntT())))
    // check that the type of the underlying expression has been changed as well
    assert(FinSetT(IntT()) == typeFinder.compute(ex))
  }

  // regression, see issue #292
  test("error on type annotation inside type annotation") {
    val typeFinder = new TrivialTypeFinder()
    val ex = tla.enumSet()
    val annotatedEx = tla.withType(ex, tla.withType(tla.enumSet(), tla.enumSet(ValEx(TlaIntSet))))
    assertThrows[TypeException] { typeFinder.inferAndSave(annotatedEx) }
  }

  // Since the introduction of BmcOper.assign, the old assignments need to be transformed
  // into the form \E t \in S: x' = t
  test("inferAndSave from the wild") {
    import IncrementalRenaming.makeName
    val init = tla.declOp(makeName("RenamedInit", 0),
        tla.and(
            tla.assignPrime(
                tla.name("recOne"),
                tla.withType(
                    tla.enumFun(
                        tla.str("x"),
                        tla.str("y")
                    ),
                    tla.enumFun(
                        tla.str("x"),
                        ValEx(TlaStrSet),
                        tla.str("y"),
                        ValEx(TlaIntSet)
                    )
                )
            ),
            tla.assignPrime(
                tla.name("recTwo"),
                tla.withType(
                    tla.enumFun(
                        tla.str("x"),
                        tla.str("x")
                    ),
                    tla.enumFun(
                        tla.str("x"),
                        ValEx(TlaStrSet),
                        tla.str("z"),
                        tla.enumSet(ValEx(TlaIntSet))
                    )
                )
            )
        ))

    val next1 = tla.declOp(makeName("RenamedNext", 0),
        tla.and(
            tla.assignPrime(
                tla.name("recOne"),
                tla.withType(
                    tla.enumFun(
                        tla.str("x"),
                        tla.str("x")
                    ),
                    tla.enumFun(
                        tla.str("x"),
                        ValEx(TlaStrSet),
                        tla.str("y"),
                        ValEx(TlaIntSet)
                    )
                )
            ),
            tla.assignPrime(
                tla.name("recTwo"),
                tla.withType(
                    tla.enumFun(
                        tla.str("x"),
                        tla.str("x")
                    ),
                    tla.enumFun(
                        tla.str("x"),
                        ValEx(TlaStrSet),
                        tla.str("z"),
                        tla.enumSet(ValEx(TlaIntSet))
                    )
                )
            )
        ))

    val next2 = tla.declOp(makeName("RenamedNext", 1),
        tla.and(
            tla.assignPrime(
                tla.name("recOne"),
                tla.withType(
                    tla.enumFun(
                        tla.str("x"),
                        tla.str("x")
                    ),
                    tla.enumFun(
                        tla.str("x"),
                        ValEx(TlaStrSet),
                        tla.str("y"),
                        ValEx(TlaIntSet)
                    )
                )
            ),
            tla.assignPrime(
                tla.name("recTwo"),
                tla.withType(
                    tla.enumFun(
                        tla.str("x"),
                        tla.str("z")
                    ),
                    tla.enumFun(
                        tla.str("x"),
                        ValEx(TlaStrSet),
                        tla.str("z"),
                        tla.enumSet(ValEx(TlaIntSet))
                    )
                )
            )
        ))

    val decls = Seq(
        init,
        next1,
        next2
    )

    val ttf = new TrivialTypeFinder

    decls foreach { d =>
      ttf.inferAndSave(d.body)
    }

    assert(ttf.typeErrors.isEmpty)
  }
}

package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.predef.TlaIntSet
import at.forsyte.apalache.tla.lir.{EnvironmentHandlerGenerator, NameEx, OperEx, ValEx}
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

  test("compute basic operators") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val p = tla.name("p")
    val set1 = tla.name("S")
    val set2 = tla.name("T")
    // good cases
    assert(BoolT() ==
      typeFinder.compute(tla.eql(set1, set2), FinSetT(IntT()), FinSetT(IntT())))
    assert(BoolT() ==
      typeFinder.compute(tla.neql(set1, set2), FinSetT(IntT()), FinSetT(IntT())))
    assert(IntT() ==
      typeFinder.compute(tla.choose(x, set1, p), IntT(), FinSetT(IntT()), BoolT()))
    assert(IntT() ==
      typeFinder.compute(tla.choose(x, p), IntT(), BoolT()))
    assert(IntT() ==
      typeFinder.compute(OperEx(TlaOper.chooseIdiom, set1), FinSetT(IntT())))
    assert(FinSetT(IntT())
      == typeFinder.compute(tla.label(set1, "lab", "a"), FinSetT(IntT()), ConstT(), ConstT()))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.eql(set1, set2), FinSetT(IntT()), FinSetT(BoolT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.neql(set1, set2), FinSetT(IntT()), FinSetT(BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() ==
        typeFinder.compute(tla.choose(x, set1, p), BoolT(), FinSetT(IntT()), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() ==
        typeFinder.compute(tla.choose(x, set1, p), IntT(), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() ==
        typeFinder.compute(tla.choose(x, set1, p), IntT(), FinSetT(IntT()), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.choose(x, p), IntT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(OperEx(TlaOper.chooseIdiom, set1), IntT()))
    }

    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT())
        == typeFinder.compute(tla.label(set1, "lab", "a"), FinSetT(IntT()), IntT(), ConstT()))
    }
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
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.uminus(i), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.plus(i, j), BoolT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.minus(i, j), BoolT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.mult(i, j), BoolT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.div(i, j), BoolT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.mod(i, j), BoolT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.exp(i, j), BoolT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.sum(i, i, j), IntT(), BoolT(), IntT()))
    }
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
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.lt(i, j), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.gt(i, j), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.le(i, j), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.ge(i, j), IntT(), BoolT()))
    }
  }

  test("compute int to X operators") {
    val typeFinder = new TrivialTypeFinder()
    val i = tla.name("i")
    val j = tla.name("j")
    // good cases
    assert(FinSetT(IntT()) == typeFinder.compute(tla.dotdot(i, j), IntT(), IntT()))
    // bad cases
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) == typeFinder.compute(tla.dotdot(i, j), IntT(), BoolT()))
    }
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
    assert(BoolT() == typeFinder.compute(tla.orParallel(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.impl(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.equiv(p, q), BoolT(), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.forall(x, S, p), IntT(), FinSetT(IntT()), BoolT()))
    assert(BoolT() == typeFinder.compute(tla.exists(x, S, p), IntT(), FinSetT(IntT()), BoolT()))
    // bad cases
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.not(p), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.and(p, q), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.or(p, q), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.orParallel(p, q), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.impl(p, q), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.equiv(p, q), IntT(), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.forall(x, S, p), IntT(), FinSetT(ConstT()), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.exists(x, S, p), IntT(), FinSetT(ConstT()), BoolT()))
    }
  }

  test("compute control operators") {
    val typeFinder = new TrivialTypeFinder()
    val p = NameEx("p")
    val q = NameEx("q")
    val x = NameEx("x")
    val y = NameEx("y")
    val z = NameEx("z")
    // good cases
    assert(FinSetT(IntT()) ==
      typeFinder.compute(tla.ite(p, x, y), BoolT(), FinSetT(IntT()), FinSetT(IntT())))
    val caseEx = tla.caseSplit(p, x, q, y)
    assert(FinSetT(IntT()) ==
      typeFinder.compute(caseEx, BoolT(), FinSetT(IntT()), BoolT(), FinSetT(IntT())))
    val caseOtherEx = tla.caseOther(z, p, x, q, y)
    assert(FinSetT(IntT()) ==
      typeFinder.compute(caseOtherEx, FinSetT(IntT()), BoolT(), FinSetT(IntT()), BoolT(), FinSetT(IntT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) ==
        typeFinder.compute(tla.ite(p, x, y), IntT(), FinSetT(IntT()), FinSetT(IntT())))
    }
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) ==
        typeFinder.compute(tla.ite(p, x, y), BoolT(), FinSetT(BoolT()), FinSetT(IntT())))
    }
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) ==
        typeFinder.compute(caseEx, BoolT(), FinSetT(IntT()), IntT(), FinSetT(IntT())))
    }
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) ==
        typeFinder.compute(caseEx, BoolT(), FinSetT(IntT()), BoolT(), FinSetT(BoolT())))
    }
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) ==
        typeFinder.compute(caseOtherEx, FinSetT(BoolT()), BoolT(), FinSetT(IntT()), BoolT(), FinSetT(IntT())))
    }
    assertThrows[TypeInferenceError] {
      assert(FinSetT(IntT()) ==
        typeFinder.compute(caseOtherEx, FinSetT(IntT()), BoolT(), FinSetT(IntT()), IntT(), FinSetT(IntT())))
    }
  }

  test("compute Boolean set operators") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // good cases
    assert(BoolT() ==
      typeFinder.compute(tla.in(int1, set12), IntT(), FinSetT(IntT())))
    assert(BoolT() ==
      typeFinder.compute(tla.notin(int1, set12), IntT(), FinSetT(IntT())))
    assert(BoolT() ==
      typeFinder.compute(tla.subset(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(BoolT() ==
      typeFinder.compute(tla.subseteq(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(BoolT() ==
      typeFinder.compute(tla.supset(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(BoolT() ==
      typeFinder.compute(tla.supseteq(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.in(set12, set12), FinSetT(IntT()), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.notin(set12, set12), FinSetT(IntT()), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.subset(int1, set12), IntT(), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.subseteq(int1, set12), IntT(), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.supset(int1, set12), IntT(), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.supseteq(int1, set12), IntT(), FinSetT(IntT()))
    }
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
    assert(FinSetT(IntT()) ==
      typeFinder.compute(tla.cup(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(FinSetT(IntT()) ==
      typeFinder.compute(tla.cap(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    assert(FinSetT(IntT()) ==
      typeFinder.compute(tla.setminus(set12, set123), FinSetT(IntT()), FinSetT(IntT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.cup(int1, set123), IntT(), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.cap(int1, set123), IntT(), FinSetT(IntT()))
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.setminus(int1, set123), IntT(), FinSetT(IntT()))
    }
  }

  test("compute set filter") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    // good cases
    assert(FinSetT(IntT()) ==
      typeFinder.compute(tla.filter(NameEx("x"), set12, tla.bool(true)),
        UnknownT(), FinSetT(IntT()), BoolT()))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.filter(NameEx("x"), int1, tla.bool(true)),
        UnknownT(), IntT(), BoolT())
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.filter(NameEx("x"), set12, int1),
        UnknownT(), FinSetT(IntT()), IntT())
    }
  }

  test("compute set map") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    // good cases
    assert(FinSetT(BoolT()) ==
      typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), set12),
        FinSetT(BoolT()), UnknownT(), FinSetT(IntT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), int1),
        FinSetT(BoolT()), UnknownT(), IntT())
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.map(tla.bool(true), NameEx("x"), set12, NameEx("y"), int1),
        FinSetT(BoolT()), UnknownT(), FinSetT(IntT()), UnknownT(), IntT())
    }
  }

  test("compute UNION") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set3 = tla.enumSet(tla.int(3))
    // good cases
    assert(FinSetT(IntT()) ==
      typeFinder.compute(tla.union(tla.enumSet(set12, set3)),
        FinSetT(FinSetT(IntT()))))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.union(set12), FinSetT(IntT()))
    }
  }

  test("compute SUBSET") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set3 = tla.enumSet(tla.int(3))

    // good cases
    assert(FinSetT(FinSetT(IntT())) ==
      typeFinder.compute(tla.powSet(set12), FinSetT(IntT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.powSet(int1), IntT())
    }
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
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.times(set12, int1), FinSetT(IntT()), IntT())
    }
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
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.funSet(set12, tla.bool(false)), FinSetT(IntT()), BoolT())
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.funSet(int1, boolSet), IntT(), FinSetT(BoolT()))
    }
  }

  test("compute [a: S, b: T]") {
    val typeFinder = new TrivialTypeFinder()
    val int1 = tla.int(1)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val boolSet = tla.enumSet(tla.bool(false), tla.bool(true))

    // good cases
    assert(FinSetT(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT()))) ==
      typeFinder.compute(tla.recSet(tla.str("a"), set12, tla.str("b"), boolSet),
        ConstT(), FinSetT(IntT()), ConstT(), FinSetT(BoolT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.recSet(tla.str("a"), int1, tla.str("b"), boolSet),
        ConstT(), IntT(), ConstT(), FinSetT(BoolT()))
    }
  }

  test("compute [a |-> 1, b |-> FALSE]") {
    val typeFinder = new TrivialTypeFinder()
    val rec = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))
    val cellType = typeFinder.compute(rec,
      ConstT(), IntT(), ConstT(), BoolT())
    assert(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT())) == cellType)
    assertThrows[TypeInferenceError] {
      typeFinder.compute(rec, IntT(), IntT(), ConstT(), BoolT())
    }
  }

  test("compute <<1, FALSE>>") {
    val typeFinder = new TrivialTypeFinder()
    val tup = tla.tuple(tla.int(1), tla.bool(false))
    val cellType = typeFinder.compute(tup, IntT(), BoolT())
    assert(TupleT(Seq(IntT(), BoolT())) == cellType)
    // an empty tuple is a sequence, but its type is unknown
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.tuple())
    }
  }

  test("compute <<1, FALSE>>[1]") {
    val typeFinder = new TrivialTypeFinder()
    val tup = tla.tuple(tla.int(1), tla.bool(false))
    val tupleType = TupleT(Seq(IntT(), BoolT()))
    assert(IntT() ==
      typeFinder.compute(tla.appFun(tup, tla.int(1)), tupleType, IntT()))
    assert(BoolT() ==
      typeFinder.compute(tla.appFun(tup, tla.int(2)), tupleType, IntT()))
    // out-of-range expressions
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.appFun(tup, tla.int(0)), tupleType, IntT())
    }
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.appFun(tup, tla.int(3)), tupleType, IntT())
    }
    // only integer constants are allowed!
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.appFun(tup, tla.name("j")), tupleType, IntT())
    }
  }

  test("compute r.a") {
    val typeFinder = new TrivialTypeFinder()
    val rec = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))
    val recType = RecordT(SortedMap("a" -> IntT(), "b" -> BoolT()))

    assert(IntT() ==
      typeFinder.compute(tla.appFun(rec, tla.str("a")), recType, ConstT()))
    assert(BoolT() ==
      typeFinder.compute(tla.appFun(rec, tla.str("b")), recType, ConstT()))
    // out-of-range expressions
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.appFun(rec, tla.str("c")), recType, ConstT())
    }
    // only string constants are allowed!
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.appFun(rec, tla.name("x")), recType, ConstT())
    }
  }

  test("compute f[x]") {
    val typeFinder = new TrivialTypeFinder()
    val fun = tla.name("f") // we know just the name
    val funType = FunT(FinSetT(IntT()), BoolT())

    assert(BoolT() ==
      typeFinder.compute(tla.appFun(fun, tla.int(1)), funType, IntT()))
    // wrong argument type
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.appFun(fun, tla.str("c")), funType, ConstT())
    }
  }

  test("compute DOMAIN fun") {
    val typeFinder = new TrivialTypeFinder()
    val fun = tla.name("f") // we know just the name
    val funType = FunT(FinSetT(BoolT()), BoolT())

    assert(FinSetT(BoolT()) == typeFinder.compute(tla.dom(fun), funType))
    // wrong argument type
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.dom(fun), BoolT())
    }
  }

  test("compute DOMAIN rec") {
    val typeFinder = new TrivialTypeFinder()
    val rec = tla.name("r") // we know just the name
    val recType = RecordT(SortedMap("a" -> IntT(), "b" -> BoolT()))

    assert(FinSetT(ConstT()) == typeFinder.compute(tla.dom(rec), recType))
    // wrong argument type
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.dom(rec), ConstT())
    }
  }

  test("compute DOMAIN tuple") {
    val typeFinder = new TrivialTypeFinder()
    val tup = tla.name("t") // we know just the name
    val tupType = TupleT(Seq(IntT(), BoolT()))

    assert(FinSetT(IntT()) == typeFinder.compute(tla.dom(tup), tupType))
    // wrong argument type
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.dom(tup), IntT())
    }
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
      typeFinder.compute(tla.funDef(e, x, S),
        BoolT(), ConstT(), FinSetT(IntT())))
    assert(FunT(FinSetT(TupleT(Seq(IntT(), ConstT()))), BoolT()) ==
      typeFinder.compute(tla.funDef(e, x, S, y, T),
        BoolT(), ConstT(), FinSetT(IntT()), ConstT(), FinSetT(ConstT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.funDef(e, x, S),
        BoolT(), ConstT(), IntT())
    }
  }

  test("compute [f EXCEPT ![e] = g]") {
    val typeFinder = new TrivialTypeFinder()
    val f = tla.name("f")
    val e = tla.name("e")
    val g = tla.name("g")
    // good cases
    val funT = FunT(FinSetT(IntT()), BoolT())
    // TlaFunOper.except expects a single index wrapped into a tuple
    assert(funT ==
      typeFinder.compute(tla.except(f, e, g),
        funT, TupleT(Seq(IntT())), BoolT()))
    val fun2T = FunT(FinSetT(TupleT(Seq(IntT(), ConstT()))), BoolT())
    assert(fun2T ==
      typeFinder.compute(tla.except(f, e, g),
        fun2T, TupleT(Seq(IntT(), ConstT())), BoolT()))
    // bad cases
    assertThrows[TypeInferenceError] {
      typeFinder.compute(tla.except(f, e, g), funT, IntT(), BoolT())
    }
  }

  test("compute FiniteSet operators") {
    val typeFinder = new TrivialTypeFinder()
    val S = tla.name("S")
    // good cases
    assert(BoolT() == typeFinder.compute(tla.isFin(S), FinSetT(IntT())))
    assert(IntT() == typeFinder.compute(tla.card(S), FinSetT(IntT())))
    // bad cases
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.isFin(S), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.card(S), IntT()))
    }
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
    assertThrows[TypeInferenceError] {
      assert(SeqT(IntT()) == typeFinder.compute(tla.head(seq), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(SeqT(IntT()) == typeFinder.compute(tla.tail(seq), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(SeqT(IntT()) == typeFinder.compute(tla.append(seq, x), SeqT(IntT()), BoolT()))
    }
    assertThrows[TypeInferenceError] {
      assert(SeqT(IntT()) == typeFinder.compute(tla.append(seq, x), IntT(), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(SeqT(IntT()) == typeFinder.compute(tla.append(seq, x), TupleT(Seq(IntT())), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(SeqT(IntT()) == typeFinder.compute(tla.concat(seq, seq), SeqT(IntT()), SeqT(BoolT())))
    }
    assertThrows[TypeInferenceError] {
      assert(IntT() == typeFinder.compute(tla.len(seq), IntT()))
    }
    assertThrows[TypeInferenceError] {
      assert(SeqT(BoolT()) == typeFinder.compute(tla.subseq(seq, x, x), SeqT(BoolT()), BoolT(), IntT()))
    }
    assertThrows[NotImplementedError] {
      assert(SeqT(BoolT()) == typeFinder.compute(tla.selectseq(seq, x), SeqT(IntT()), BoolT()))
    }
  }

  test("compute TLC operators") {
    val typeFinder = new TrivialTypeFinder()
    val e = tla.name("e")
    val msg = "message"
    // good cases:
    // We only allow assert to return a Boolean result.
    // When you use assert in a non-Boolean expression, provide the tool with a type annotation.
    assert(BoolT() == typeFinder.compute(tla.assert(e, msg), BoolT(), ConstT()))
    // bad cases
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.assert(e, msg), IntT(), ConstT()))
    }
    assertThrows[TypeInferenceError] {
      assert(BoolT() == typeFinder.compute(tla.assert(e, msg), BoolT(), IntT()))
    }
  }

  test("inferAndSave variable assignment") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    val assignByIn = tla.in(tla.prime(x), tla.enumSet(tla.int(1)))
    assert(typeFinder.inferAndSave(assignByIn).contains(BoolT()))
    assert(IntT() == typeFinder.getVarTypes("x'"))
    val assignByEq = tla.eql(tla.prime(y), tla.enumSet(tla.int(1)))
    assert(typeFinder.inferAndSave(assignByEq).contains(BoolT()))
    assert(FinSetT(IntT()) == typeFinder.getVarTypes("y'"))
  }

  test("inferAndSave double assignment") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    // double assignment is fine as soon as the types are preserved
    val assignByIn =
      tla.or(
        tla.in(tla.prime(x), tla.enumSet(tla.int(1))),
        tla.in(tla.prime(x), tla.enumSet(tla.int(3))))
    assert(typeFinder.inferAndSave(assignByIn).contains(BoolT()))
    assert(IntT() == typeFinder.getVarTypes("x'"))

    val assignByEq =
      tla.or(
        tla.eql(tla.prime(y), tla.enumSet(tla.int(1))),
        tla.eql(tla.prime(y), tla.enumSet(tla.int(4))))
    assert(typeFinder.inferAndSave(assignByEq).contains(BoolT()))
    assert(FinSetT(IntT()) == typeFinder.getVarTypes("y'"))
  }

  test("inferAndSave set filter") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val filter = tla.filter(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(filter).contains(FinSetT(IntT())))
    assert(IntT() == typeFinder.getVarTypes("x"))
  }

  test("inferAndSave set map") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    val map = tla.map(tla.enumSet(x), x, tla.enumSet(tla.int(3)))
    assert(typeFinder.inferAndSave(map).contains(FinSetT(FinSetT(IntT()))))
    assert(IntT() == typeFinder.getVarTypes("x"))
  }

  test("inferAndSave exists/forall") {
    var typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val exists = tla.exists(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(exists).contains(BoolT()))
    assert(IntT() == typeFinder.getVarTypes("x"))
    typeFinder = new TrivialTypeFinder()
    val forall = tla.exists(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(forall).contains(BoolT()))
    assert(IntT() == typeFinder.getVarTypes("x"))
    // bad cases
    typeFinder = new TrivialTypeFinder()
    assert(typeFinder.inferAndSave(tla.exists(x, tla.enumSet(tla.int(3)), tla.int(4))).isEmpty)
    assert(typeFinder.getTypeErrors.nonEmpty)
  }

  test("inferAndSave CHOOSE") {
    var typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val choose = tla.choose(x, tla.enumSet(tla.int(3)), tla.bool(true))
    assert(typeFinder.inferAndSave(choose).contains(IntT()))
    assert(IntT() == typeFinder.getVarTypes("x"))
    // bad cases
    typeFinder = new TrivialTypeFinder()
    val badChoose = tla.choose(x, tla.enumSet(tla.int(3)), tla.int(4))
    assert(typeFinder.inferAndSave(badChoose).isEmpty)
    assert(typeFinder.getTypeErrors.nonEmpty)
  }

  test("inferAndSave [x \\in S |-> e]") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val map = tla.funDef(tla.enumSet(x), x, tla.enumSet(tla.int(1)))
    assert(typeFinder.inferAndSave(map).contains(FunT(FinSetT(IntT()), FinSetT(IntT()))))
    assert(IntT() == typeFinder.getVarTypes("x"))
  }

  test("inferAndSave [x \\in S, y \\in T |-> e]") {
    val typeFinder = new TrivialTypeFinder()
    val x = tla.name("x")
    val y = tla.name("y")
    val map = tla.funDef(tla.enumSet(x), x, tla.enumSet(tla.int(1)), y, tla.enumSet(tla.bool(false)))
    assert(typeFinder.inferAndSave(map).contains(FunT(FinSetT(TupleT(Seq(IntT(), BoolT()))), FinSetT(IntT()))))
    assert(IntT() == typeFinder.getVarTypes("x"))
    assert(BoolT() == typeFinder.getVarTypes("y"))
  }

  test("inferAndSave type annotation") {
    val typeFinder = new TrivialTypeFinder()
    val ex = tla.enumSet()
    // assign an id to ex
    val handler = EnvironmentHandlerGenerator.makeEH
    handler.identify(ex)

    val annotatedEx = tla.withType(ex, tla.enumSet(ValEx(TlaIntSet)))
    assert(typeFinder.inferAndSave(annotatedEx).contains(FinSetT(IntT())))
    // check that the type of the underlying expression has been changed as well
    assert(FinSetT(IntT()) == typeFinder.compute(ex))
  }
}
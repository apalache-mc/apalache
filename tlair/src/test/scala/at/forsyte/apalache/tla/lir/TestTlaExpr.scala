package at.forsyte.apalache.tla.lir

import javax.imageio.metadata.IIOMetadataFormat

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaEmptySet}
import at.forsyte.apalache.tla.lir.values.{TlaUserSet, TlaStr, TlaInt}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
 * Tests for the TLA+ expressions that we can construct.
 */
@RunWith(classOf[JUnitRunner])
class TestTlaExpr extends FunSuite {
  test("create a conjunction") {
    val x = ValEx(new TlaVar("x"))
    val y = ValEx(new TlaVar("y"))
    val e = OperEx(TlaBoolOper.and, x, y)

    e match {
      case OperEx(TlaBoolOper.and, ValEx(i: TlaVar), ValEx(j: TlaVar)) =>
        assert(i.name == "x")
        assert(j.name == "y")
    }
  }

  test("using set operations") {
    // x = {1, 2, "hello"}
    val x = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaStr("hello")))
    // y = {4}
    val y = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4)))
    // x \cup y
    OperEx(TlaSetOper.cup, x, y)
    // x \cap y
    OperEx(TlaSetOper.cap, x, y)
    // x \in y
    OperEx(TlaSetOper.in, x, y)
    // x \notin y
    OperEx(TlaSetOper.notin, x, y)
    // x \setminus y
    OperEx(TlaSetOper.setminus, x, y)
    // x \subset y
    OperEx(TlaSetOper.subset, x, y)
    // x \subseteq y
    OperEx(TlaSetOper.subseteq, x, y)
    // x \supset y
    OperEx(TlaSetOper.supset, x, y)
    // x \supseteq y
    OperEx(TlaSetOper.supseteq, x, y)
    // SUBSET y
    OperEx(TlaSetOper.powerset, y)
    // UNION x
    OperEx(TlaSetOper.union, x)
    // { i \in x : i \in y }
    val i = ValEx(new TlaVar("i"))
    OperEx(TlaSetOper.filter, i, x, OperEx(TlaSetOper.in, i, y))
    // { i \cup y : i \in x }
    OperEx(TlaSetOper.map, OperEx(TlaSetOper.cup, i, y), i, x)
  }

  test("wrong arity in set operations") {
    // x = {1, 2, "hello"}
    val x = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaStr("hello")))
    // y = {4}
    val y = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4)))

    def expectWrongArity(op: TlaOper, args: TlaEx*) = {
      try {
        OperEx(op, args:_*)
        fail("Expected an IllegalArgumentException")
      } catch { case _: IllegalArgumentException => }
    }
    // x \cup y y
    expectWrongArity(TlaSetOper.cup, x, y, y)
    // x \cap y
    expectWrongArity(TlaSetOper.cap, x, y, y)
    // x \in y
    expectWrongArity(TlaSetOper.in, x)
    // x \notin y
    expectWrongArity(TlaSetOper.notin, y)
    // x \setminus y
    expectWrongArity(TlaSetOper.setminus, y)
    // x \subset y
    expectWrongArity(TlaSetOper.subset, x)
    // x \subseteq y
    expectWrongArity(TlaSetOper.subseteq, x)
    // x \supset y
    expectWrongArity(TlaSetOper.supset, x)
    // x \supseteq y
    expectWrongArity(TlaSetOper.supseteq, x)
    // SUBSET y
    expectWrongArity(TlaSetOper.powerset, y, x)
    // UNION x
    expectWrongArity(TlaSetOper.union, x, y)
  }

  test("the empty set") {
    // this is the way to use the empty set
    TlaEmptySet()
    // this is the wrong way to define the empty set
    try {
      OperEx(TlaSetOper.enumSet)
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }

    // an intersection with another set
    OperEx(TlaSetOper.cap,
      ValEx(TlaEmptySet()),
      OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)))
    )
  }

  test("set constructors") {
    // declare sets whose contents we don't know
    val set1 = new TlaUserSet()
    val set2 = new TlaUserSet()
    // there is only one set of integers
    val intSet = TlaIntSet()

    val rhs = OperEx(TlaSetOper.cup, ValEx(set2), ValEx(intSet))
    OperEx(TlaOper.eq, ValEx(set1), rhs)
  }

  test("strange set operations") {
    // We can write something like 2 \cup {4}. TLA Toolbox would not complain.
    OperEx(TlaSetOper.cup,
      ValEx(TlaInt(2)),
      OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4))))
  }

  test("declaring an order 0 operator") {
    val odef = new TlaOperDef("A", List(),
      OperEx(TlaBoolOper.and,
        OperEx(TlaActionOper.tlaPrime, ValEx(new TlaVar("x"))),
        ValEx(new TlaVar("y"))
      )
    )

    // this is the way to use a user-defined operator
    val applyA = odef.createOperator()
    OperEx(applyA)

    // we should get an exception when the number of arguments is incorrect
    try {
      OperEx(applyA, ValEx(new TlaVar("a")))
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }
  }

  test("declaring an order 1 operator") {
    val odef = new TlaOperDef("A", List(new SimpleParam("x"), new SimpleParam("y")),
      OperEx(TlaBoolOper.and,
        OperEx(TlaActionOper.tlaPrime, ValEx(new TlaVar("x"))),
        ValEx(new TlaVar("y"))
      )
    )

    // this is the way to use a user-defined operator
    val applyA = odef.createOperator()
    OperEx(applyA, ValEx(new TlaVar("a")), ValEx(new TlaVar("b")))

    // we should get an exception when the number of arguments is incorrect
    try {
      OperEx(applyA, ValEx(new TlaVar("a")))
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }
  }

  test("compatibility of the signatures") {
    // f(_, _)
    val fOper = new OperParam("f", FixedArity(2))

    try {
      OperEx(TlaSetOper.cup, OperRefEx(fOper), OperRefEx(fOper))
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }
  }

  test("declaring an order 2 operator") {
    // f(_, _)
    val fOper = new OperParam("f", FixedArity(2))

    // A(f(_, _), x, y) == f(x, y)
    val odef = new TlaOperDef("A", List(fOper, new SimpleParam("x"), new SimpleParam("y")),
      OperEx(fOper,
        ValEx(new TlaVar("x")),
        ValEx(new TlaVar("y"))
      )
    )

    // this is the way to use a user-defined operator
    val applyA = odef.createOperator()
    OperEx(applyA, OperRefEx(TlaSetOper.cup), ValEx(new TlaVar("a")), ValEx(new TlaVar("b")))

    // we should get an exception when passing anything different from OperRefEx as the first argument
    try {
      OperEx(applyA, ValEx(new TlaVar("a")), ValEx(new TlaVar("b")), ValEx(new TlaVar("b")))
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }
  }
}

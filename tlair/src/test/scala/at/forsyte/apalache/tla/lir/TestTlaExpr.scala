package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
 * Tests for the TLA+ expressions that we can construct.
 */
@RunWith(classOf[JUnitRunner])
class TestTlaExpr extends FunSuite {
  test("no type tag") {
    // this expression is constructed with the implicit value for typeTag = Untyped().
    val ex = ValEx(TlaInt(42))
    // pattern matching should work without worrying about type tags
    ex match {
      case matched @ ValEx(TlaInt(i)) =>
        assert(42 == i)
        assert(Untyped() == matched.typeTag)

      case _ =>
        fail("Expected valEx")
    }
  }

  test("type tag") {
    // this expression is annotated with a type tag. For testing purposes, the type tag is just a string.
    val ex = ValEx(TlaInt(42))(Typed[String]("foo"))
    // although we have have set a type tag, pattern matching should be oblivious to that
    ex match {
      case matched @ ValEx(TlaInt(i)) =>
        assert(42 == i)
        // we can extract the type, whenever we want to do it
        assert(Typed[String]("foo") == matched.typeTag)

      case _ =>
        fail("Expected ValEx")
    }
  }

  test("create a conjunction") {
    val x = NameEx("x")
    val y = NameEx("y")
    val e = OperEx(TlaBoolOper.and, x, y)

    e match {
      case OperEx(TlaBoolOper.and, NameEx(i: String), NameEx(j: String)) =>
        assert(i == "x")
        assert(j == "y")
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
    // x \subseteq y
    OperEx(TlaSetOper.subseteq, x, y)
    // SUBSET y
    OperEx(TlaSetOper.powerset, y)
    // UNION x
    OperEx(TlaSetOper.union, x)
    // { i \in x : i \in y }
    val i = NameEx("i")
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
        OperEx(op, args: _*)
        fail("Expected an IllegalArgumentException")
      } catch {
        case _: IllegalArgumentException =>
      }
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
    // x \subseteq y
    expectWrongArity(TlaSetOper.subseteq, x)
    // SUBSET y
    expectWrongArity(TlaSetOper.powerset, y, x)
    // UNION x
    expectWrongArity(TlaSetOper.union, x, y)
  }

  test("the empty set") {
    // this is the old way to use the only empty set, not anymore
    // TlaEmptySet
    // this is the wrong way to define the empty set
    OperEx(TlaSetOper.enumSet)

    // an intersection with another set
    OperEx(TlaSetOper.cap, OperEx(TlaSetOper.enumSet), OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1))))
  }

  test("strange set operations") {
    // We can write something like 2 \cup {4}. TLA Toolbox would not complain.
    OperEx(TlaSetOper.cup, ValEx(TlaInt(2)), OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4))))
  }

  test("declaring an order 0 operator") {
    // A == x' /\ y
    val odef = TlaOperDecl("A", List(), OperEx(TlaBoolOper.and, OperEx(TlaActionOper.prime, NameEx("x")), NameEx("y")))

    // this is the way to use a user-defined operator
    tla.appDecl(odef)

    // we should get an exception when the number of arguments is incorrect
    try {
      tla.appDecl(odef, NameEx("a"))
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }
  }

  test("declaring an order 1 operator") {
    // A(x, y) == x' /\ y
    val odef = TlaOperDecl("A", List(SimpleFormalParam("x"), SimpleFormalParam("y")),
        OperEx(TlaBoolOper.and, OperEx(TlaActionOper.prime, NameEx("x")), NameEx("y")))

    // this is the way to use a user-defined operator
    tla.appDecl(odef, NameEx("a"), NameEx("b"))

    // we should get an exception when the number of arguments is incorrect
    try {
      tla.appDecl(odef, NameEx("a"))
      fail("Expected an IllegalArgumentException")
    } catch {
      case _: IllegalArgumentException => () // OK
    }
  }

  test("declaring an order 2 operator") {
    // f(_, _)
    val fOper = OperFormalParam("f", 2)

    // A(f(_, _), x, y) == f(x, y)
    val odef = TlaOperDecl("A", List(fOper, SimpleFormalParam("x"), SimpleFormalParam("y")),
        OperEx(TlaOper.apply, NameEx("f"), NameEx("x"), NameEx("y")))

    // this is the way to use a user-defined operator
    tla.appDecl(odef, NameEx(TlaSetOper.cup.name), NameEx("a"), NameEx("b"))

    // The following expression does not make a lot of sense, but it is legal to construct it.
    // Later, there will be a plugin to detect inconsistent expressions like this.
    tla.appDecl(odef, NameEx("a"), NameEx("b"), NameEx("b"))
  }

  test("existentials") {
    val ex1 =
      OperEx(TlaBoolOper.existsUnbounded, NameEx("x"), OperEx(TlaOper.eq, NameEx("x"), NameEx("x")))
    val ex2 =
      OperEx(TlaBoolOper.existsUnbounded, NameEx("x"), OperEx(TlaOper.eq, NameEx("x"), NameEx("x")))
    val conj = OperEx(TlaBoolOper.and, ex1, ex2)
  }

}

package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

/**
 * Tests for the TLA+ expressions that we can construct.
 */
@RunWith(classOf[JUnitRunner])
class TestTlaExpr extends AnyFunSuite {
  test("no type tag") {
    // this expression is constructed with the implicit value for typeTag = Untyped.
    val ex = ValEx(TlaInt(42))
    // pattern matching should work without worrying about type tags
    ex match {
      case matched @ ValEx(TlaInt(i)) =>
        assert(42 == i)
        assert(Untyped == matched.typeTag)

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
      case invalid => fail(s"invalid result when constructing conjunction: $invalid")
    }
  }

  test("set operators accept their valid arities") {
    // x = {1, 2, "hello"}
    val x = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaStr("hello")))
    // y = {4}
    val y = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4)))
    val i = NameEx("i")
    val cases = Seq(
        TlaSetOper.cup -> Seq(x, y),
        TlaSetOper.cap -> Seq(x, y),
        TlaSetOper.in -> Seq(x, y),
        TlaSetOper.notin -> Seq(x, y),
        TlaSetOper.setminus -> Seq(x, y),
        TlaSetOper.subseteq -> Seq(x, y),
        TlaSetOper.powerset -> Seq(y),
        TlaSetOper.union -> Seq(x),
        TlaSetOper.filter -> Seq(i, x, OperEx(TlaSetOper.in, i, y)),
        TlaSetOper.map -> Seq(OperEx(TlaSetOper.cup, i, y), i, x),
    )

    cases.foreach { case (operator, args) =>
      val expression = OperEx(operator, args: _*)
      assert(expression.oper == operator)
      assert(expression.args == args)
    }
  }

  test("wrong arity in set operations") {
    // x = {1, 2, "hello"}
    val x = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaStr("hello")))
    // y = {4}
    val y = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4)))

    def expectWrongArity(op: TlaOper, args: TlaEx*): Unit = {
      assertThrows[IllegalArgumentException] {
        OperEx(op, args: _*)
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

  test("the empty set is represented by a nullary set enumeration") {
    val emptySet = OperEx(TlaSetOper.enumSet)
    val singleton = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)))
    val intersection = OperEx(TlaSetOper.cap, emptySet, singleton)

    assert(emptySet.args.isEmpty)
    assert(intersection.args == Seq(emptySet, singleton))
  }

  test("expression construction does not enforce operand types") {
    val integer = ValEx(TlaInt(2))
    val set = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(4)))
    val expression = OperEx(TlaSetOper.cup, integer, set)

    assert(expression.args == Seq(integer, set))
  }

  test("declaring an order 0 operator") {
    // A == x' /\ y
    val odef = TlaOperDecl("A", List(), OperEx(TlaBoolOper.and, OperEx(TlaActionOper.prime, NameEx("x")), NameEx("y")))

    val application = tla.appDecl(odef).untyped()
    assert(application == OperEx(TlaOper.apply, NameEx("A")))

    assertThrows[IllegalArgumentException] {
      tla.appDecl(odef, NameEx("a"))
    }
  }

  test("declaring an order 1 operator") {
    // A(x, y) == x' /\ y
    val odef = TlaOperDecl("A", List(OperParam("x"), OperParam("y")),
        OperEx(TlaBoolOper.and, OperEx(TlaActionOper.prime, NameEx("x")), NameEx("y")))

    val application = tla.appDecl(odef, NameEx("a"), NameEx("b")).untyped()
    assert(application == OperEx(TlaOper.apply, NameEx("A"), NameEx("a"), NameEx("b")))

    assertThrows[IllegalArgumentException] {
      tla.appDecl(odef, NameEx("a"))
    }
  }

  test("declaring an order 2 operator") {
    // f(_, _)
    val fOper = OperParam("f", 2)

    // A(f(_, _), x, y) == f(x, y)
    val odef = TlaOperDecl("A", List(fOper, OperParam("x"), OperParam("y")),
        OperEx(TlaOper.apply, NameEx("f"), NameEx("x"), NameEx("y")))

    val builtInApplication =
      tla.appDecl(odef, NameEx(TlaSetOper.cup.name), NameEx("a"), NameEx("b")).untyped()
    assert(builtInApplication ==
      OperEx(TlaOper.apply, NameEx("A"), NameEx(TlaSetOper.cup.name), NameEx("a"), NameEx("b")))

    // The following expression does not make a lot of sense, but it is legal to construct it.
    // Later, there will be a plugin to detect inconsistent expressions like this.
    val uncheckedApplication = tla.appDecl(odef, NameEx("a"), NameEx("b"), NameEx("b")).untyped()
    assert(uncheckedApplication == OperEx(TlaOper.apply, NameEx("A"), NameEx("a"), NameEx("b"), NameEx("b")))
  }

}

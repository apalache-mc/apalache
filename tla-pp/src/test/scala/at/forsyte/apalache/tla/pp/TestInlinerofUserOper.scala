package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestInlinerofUserOper extends FunSuite {

  import tla._

  test("Test Inline") {
    val types =
      Map("i" -> IntT1(), "b" -> BoolT1(), "U" -> OperT1(Seq(), IntT1()), "C" -> OperT1(Seq(IntT1()), IntT1()))
    val cBody = plus(name("x") ? "i", int(1))
      .typed(types, "i")
    // C(x) == x + 1
    // B == k
    // A == B()
    val cDecl = declOp("C", cBody, OperParam("x"))
      .typedOperDecl(types, "C")
    val aDecl = declOp("A", appOp(name("B") ? "U") ? "i")
      .typedOperDecl(types, "U")
    val bDecl = declOp("B", name("k") ? "i")
      .typedOperDecl(types, "U")

    val operDecls = Seq(aDecl, bDecl, cDecl)

    val bodies = BodyMapFactory.makeFromDecls(operDecls)

    val transformation = InlinerOfUserOper(bodies, new IdleTracker())

    // B
    val ex1 = tla
      .name("B")
      .typed(types, "U")
    // B()
    val ex2 = appOp(name("B") ? "U")
      .typed(types, "i")
    // A
    val ex3 = tla
      .name("A")
      .typed(types, "U")
    // A()
    val ex4 = appOp(name("A") ? "U")
      .typed(types, "i")
    // 1 = 0 \/ C(A()) >= 0
    val ex5 = or(
        eql(int(1), int(0)) ? "b",
        ge(appOp(name("C") ? "C", appOp(name("A") ? "U") ? "i") ? "i", int(0)) ? "b",
    )
      .typed(types, "b")
    // LET X == C(p) IN X()
    val ex6 = letIn(
        appOp(name("X") ? "U") ? "i",
        declOp("X", appOp(name("C") ? "C", name("p") ? "i") ? "i")
          .typedOperDecl(types, "U"),
    ).typed(types, "i")

    // no inlining, as B is just passed by name
    val expected1 = name("B").typed(types, "U")
    val expected2 = name("k").typed(types, "i")
    val expected3 = name("A").typed(types, "U")
    val expected4 = name("k").typed(types, "i")
    // the bodies of A and C are inlined
    val expected5 = or(
        eql(int(1), int(0)) ? "b",
        ge(plus(name("k") ? "i", int(1)) ? "i", int(0)) ? "b",
    ).typed(types, "b")
    // C is inlined, but X is not
    val expected6 = letIn(
        appOp(name("X") ? "U") ? "i",
        declOp("X", plus(name("p") ? "i", int(1)) ? "i")
          .typedOperDecl(types, "U"),
    ).typed(types, "i")

    assert(expected1 == transformation(ex1))
    assert(expected2 == transformation(ex2))
    assert(expected3 == transformation(ex3))
    assert(expected4 == transformation(ex4))
    assert(expected5 == transformation(ex5))
    assert(expected6 == transformation(ex6))

    val applyCwithNoArgs = appOp(name("C") ? "U").typed(types, "i")
    val applyCwithTwoArgs = appOp(name("C") ? "U", name("a") ? "i", name("b") ? "i")
      .typed(types, "i")
    assertThrows[IllegalArgumentException] {
      transformation(applyCwithNoArgs)
    }
    assertThrows[IllegalArgumentException] {
      transformation(applyCwithTwoArgs)
    }
  }

  // disable this test for a moment
  test("Instantiate and unify type variables when inlining") {
    val types =
      Map("i" -> IntT1(), "b" -> BoolT1(), "c" -> VarT1("c"), "Sc" -> SetT1(VarT1("c")),
          "SSc" -> SetT1(SetT1(VarT1("c"))), "U" -> OperT1(Seq(), IntT1()), "Si" -> SetT1(IntT1()),
          "SSi" -> SetT1(SetT1(IntT1())), "C" -> OperT1(Seq(VarT1("c")), SetT1(VarT1("c"))),
          "B" -> OperT1(Seq(SetT1(VarT1("c"))), SetT1(SetT1(VarT1("c")))), "A" -> OperT1(Seq(), SetT1(SetT1(IntT1()))))
    // @type: c => Set(c);
    // C(x) == { x }
    // @type: Set(c) => Set(Set(c));
    // B(x) == C(x) \\union {}
    // @type: () => Set(Set(Int));
    // A == B({ 1 })
    //
    // A()
    val bodyOfC = enumSet(name("x") ? "c")
      .typed(types, "Sc")
    val declOfC = declOp("C", bodyOfC, OperParam("x"))
      .typedOperDecl(types, "C")
    val bodyOfB = cup(appOp(name("C") ? "C", name("x") ? "Sc") ? "SSc", enumSet() ? "SSc")
      .typed(types, "SSc")
    val declOfB = declOp("B", bodyOfB, OperParam("x"))
      .typedOperDecl(types, "B")
    val bodyOfA = appOp(name("B") ? "B", enumSet(int(1)) ? "Si")
      .typed(types, "SSi")
    val declOfA = declOp("A", bodyOfA)
      .typedOperDecl(types, "A")

    val operDecls = Seq(declOfC, declOfB, declOfA)
    val bodies = BodyMapFactory.makeFromDecls(operDecls)
    val transformation = InlinerOfUserOper(bodies, new IdleTracker())
    val ex1 = appOp(name("A") ? "A")
      .typed(types, "SSi")
    val expected1 = cup(enumSet(enumSet(tla.int(1)) ? "Si") ? "SSi", enumSet() ? "SSi").typed(types, "SSi")

    val result1 = transformation(ex1)
    assert(expected1.eqTyped(result1))
  }
}

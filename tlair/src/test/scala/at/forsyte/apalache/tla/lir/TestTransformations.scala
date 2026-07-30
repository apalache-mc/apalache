package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaControlOper, TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.TlaExTransformation
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.transformations.decorateWithPrime
import at.forsyte.apalache.tla.lir.values.TlaBool
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.Outcome

import java.io.{File, FileOutputStream, PrintStream}

@RunWith(classOf[JUnitRunner])
class TestTransformations extends AnyFunSuite {

  override protected def withFixture(test: NoArgTest): Outcome = {
    // Tmp file to capture the noisy stdout from these tests
    // otherwise they pollut stdout on our CI making it hard to see failures
    val tmp = File.createTempFile("tlair-test-output-", ".tmp")
    tmp.deleteOnExit()

    try {
      System.setOut(new PrintStream(new FileOutputStream(tmp)))
      super.withFixture(test)
    } finally {
      System.setOut(System.out)
    }

  }

  import tla._

  test("Test Prime") {
    val vars: Set[String] = Set(
        "x",
        "a",
    )
    val transformation = decorateWithPrime(vars, new IdleTracker())

    val a = tla.name("a")
    val x = tla.name("x")
    val y = tla.name("y")

    val pa1: (TlaEx, TlaEx) = x.untyped() -> prime(x).untyped()
    val pa2: (TlaEx, TlaEx) = y.untyped() -> y.untyped()
    val pa3 = prime(x).untyped() -> prime(x).untyped()
    val pa4 = and(x, y, prime(a)).untyped() -> and(prime(x), y, prime(a)).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
    )
    val cmp = expected.map { case (k, v) =>
      (v, transformation(k))
    }
    cmp.foreach { case (ex, act) =>
      assert(ex == act)
    }
  }

  test("Test Flatten") {
    val transformation = Flatten(new IdleTracker())

    val A = tla.name("A")
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val e = tla.name("e")
    val f = tla.name("f")
    val g = tla.name("g")
    val h = NameEx("h")
    val x = tla.name("x")
    val y = tla.name("y")
    val z = tla.name("z")

    val pa1: (TlaEx, TlaEx) = x.untyped() -> x.untyped()
    val pa2 = and(x, and(y, z)).untyped() -> and(x, y, z).untyped()
    val pa3 = or(x, or(y, z)).untyped() -> or(x, y, z).untyped()
    val pa4 = or(x, and(y, z)).untyped() -> or(x, and(y, z)).untyped()
    val pa5 = and(
        and(
            or(
                or(a, b),
                or(c, d),
            )
        ),
        and(
            or(
                or(e, f),
                or(g, h),
            )
        ),
    ).untyped() -> and(
        or(a, b, c, d),
        or(e, f, g, h),
    ).untyped()
    val pa6 = enumSet(or(x, and(y, z))).untyped() -> enumSet(or(x, and(y, z))).untyped()
    val pa7 = letIn(
        appOp(A),
        declOp("A", int(1)).untypedOperDecl(),
    ).untyped() -> letIn(
        appOp(A),
        declOp("A", int(1)).untypedOperDecl(),
    ).untyped()

    val pa8 = letIn(
        appOp(A),
        declOp("A", or(x, or(y, z))).untypedOperDecl(),
    ).untyped() -> letIn(
        appOp(A),
        declOp("A", or(x, y, z)).untypedOperDecl(),
    ).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
        pa6,
        pa7,
        pa8,
    )
    val cmp = expected.map { case (k, v) =>
      (v, transformation(k))
    }
    cmp.foreach { case (ex, act) =>
      assert(ex == act)
    }
  }

  // Regression tests for preserving the original `typeTag` when Flatten
  // rebuilds an expression whose children changed.

  // We need an integer literal with a real Int type tag for the regression
  // tests below, because the implicit `IntTag` is Untyped in this file
  // (UntypedPredefs is in scope to keep the older tests working).
  private val intOne: TlaEx = ValEx(values.TlaInt(1))(Typed(IntT1))
  private val trueEx: TlaEx = ValEx(TlaBool(true))(Typed(BoolT1))

  // Nested binary OR matching how SANY parses `TRUE \/ TRUE \/ TRUE`.
  private def nestedOr3(): TlaEx =
    OperEx(
        TlaBoolOper.or,
        OperEx(TlaBoolOper.or, trueEx, trueEx)(Typed(BoolT1)),
        trueEx,
    )(Typed(BoolT1))

  // Flat 3-ary OR, what Flatten should produce.
  private def flatOr3(): TlaEx =
    OperEx(TlaBoolOper.or, trueEx, trueEx, trueEx)(Typed(BoolT1))

  private def nestedAnd3(): TlaEx =
    OperEx(
        TlaBoolOper.and,
        OperEx(TlaBoolOper.and, trueEx, trueEx)(Typed(BoolT1)),
        trueEx,
    )(Typed(BoolT1))

  private def flatAnd3(): TlaEx =
    OperEx(TlaBoolOper.and, trueEx, trueEx, trueEx)(Typed(BoolT1))

  // The Bool tag explicitly mirrors the call site in
  // tla-pp/.../temporal/utils.scala andInDecl, where Flatten is invoked as
  // `Flatten(tracker)(Typed(BoolT1))(...)`. We pass it explicitly here to
  // avoid an ambiguous implicit with the file-wide UntypedPredefs import.
  private def flattenWithBoolImplicit: TlaExTransformation =
    Flatten(new IdleTracker())(Typed(BoolT1))

  test("Flatten preserves typeTag on a rebuilt SET_FILTER (regression for apalache-mc/apalache#2107)") {
    val transformation = flattenWithBoolImplicit

    val xName = NameEx("x")(Typed(IntT1))
    val setOne = OperEx(TlaSetOper.enumSet, intOne)(Typed(SetT1(IntT1)))

    // { x \in {1} : TRUE \/ TRUE \/ TRUE }  (parsed as nested OR)
    val filterIn = OperEx(TlaSetOper.filter, xName, setOne, nestedOr3())(Typed(SetT1(IntT1)))

    val filterOut = transformation(filterIn)

    // 1) The set-filter must still be a Set(Int), not the Bool implicit.
    assert(filterOut.typeTag == Typed(SetT1(IntT1)), s"SET_FILTER lost its Set(Int) typeTag; got ${filterOut.typeTag}")
    // 2) Predicate must be flattened.
    filterOut match {
      case OperEx(TlaSetOper.filter, _, _, pred) =>
        assert(pred == flatOr3(), s"Predicate was not flattened: $pred")
        assert(pred.typeTag == Typed(BoolT1))
      case _ => fail(s"Unexpected shape after Flatten: $filterOut")
    }
  }

  test("Flatten preserves typeTag on a rebuilt IF-THEN-ELSE returning a Set") {
    val transformation = flattenWithBoolImplicit

    val setOne = OperEx(TlaSetOper.enumSet, intOne)(Typed(SetT1(IntT1)))
    val emptySet = OperEx(TlaSetOper.enumSet)(Typed(SetT1(IntT1)))

    // IF (TRUE /\ TRUE) /\ TRUE THEN {1} ELSE {}
    val ite = OperEx(TlaControlOper.ifThenElse, nestedAnd3(), setOne, emptySet)(Typed(SetT1(IntT1)))

    val out = transformation(ite)

    assert(out.typeTag == Typed(SetT1(IntT1)), s"IF-THEN-ELSE lost its Set(Int) typeTag; got ${out.typeTag}")
    // The nested AND inside the condition must be flattened.
    out match {
      case OperEx(TlaControlOper.ifThenElse, cond, _, _) =>
        assert(cond == flatAnd3(), s"Condition was not flattened: $cond")
      case _ => fail(s"Unexpected shape after Flatten: $out")
    }

    // Also check that the SET_IN parent and its rebuilt IF child keep their own tags.
    val setIn = OperEx(TlaSetOper.in, intOne, ite)(Typed(BoolT1))
    val outIn = transformation(setIn)
    assert(outIn.typeTag == Typed(BoolT1))
    outIn match {
      case OperEx(TlaSetOper.in, _, innerIte) =>
        assert(innerIte.typeTag == Typed(SetT1(IntT1)), s"Inner IF lost its Set(Int) typeTag; got ${innerIte.typeTag}")
      case _ => fail(s"Unexpected shape: $outIn")
    }
  }

  test("Flatten preserves typeTag on a rebuilt LET-IN returning a Set") {
    val transformation = flattenWithBoolImplicit

    val setOne = OperEx(TlaSetOper.enumSet, intOne)(Typed(SetT1(IntT1)))
    val emptySet = OperEx(TlaSetOper.enumSet)(Typed(SetT1(IntT1)))
    val body = OperEx(TlaControlOper.ifThenElse, nestedAnd3(), setOne, emptySet)(Typed(SetT1(IntT1)))
    val letIn = LetInEx(body, TlaOperDecl("A", List.empty, trueEx))(Typed(SetT1(IntT1)))

    val out = transformation(letIn)

    assert(out.typeTag == Typed(SetT1(IntT1)), s"LET-IN lost its Set(Int) typeTag; got ${out.typeTag}")
    out match {
      case LetInEx(OperEx(TlaControlOper.ifThenElse, cond, _, _), _*) =>
        assert(cond == flatAnd3(), s"LET-IN body was not flattened: $cond")
      case _ => fail(s"Unexpected shape after Flatten: $out")
    }
  }

  test("Flatten preserves typeTag on a rebuilt function constructor") {
    val transformation = flattenWithBoolImplicit

    val pName = NameEx("p")(Typed(IntT1))
    val setOne = OperEx(TlaSetOper.enumSet, intOne)(Typed(SetT1(IntT1)))
    val falseEx = ValEx(TlaBool(false))(Typed(BoolT1))
    val body = OperEx(TlaControlOper.ifThenElse, nestedAnd3(), falseEx, falseEx)(Typed(BoolT1))
    val funCtor = OperEx(TlaFunOper.funDef, body, pName, setOne)(Typed(FunT1(IntT1, BoolT1)))

    val out = transformation(funCtor)

    assert(out.typeTag == Typed(FunT1(IntT1, BoolT1)),
        s"Function constructor lost its Fun(Int, Bool) typeTag; got ${out.typeTag}")
  }
}

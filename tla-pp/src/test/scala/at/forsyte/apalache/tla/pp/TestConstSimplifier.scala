package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.convenience._
import at.forsyte.apalache.tla.typecomp.{build, TBuilderInstruction}
import at.forsyte.apalache.tla.lir.convenience.{tla => oldTla}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.{AppendedClues, BeforeAndAfterEach}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

/**
 * Tests for ConstSimplifier.
 */
@RunWith(classOf[JUnitRunner])
class TestConstSimplifier extends AnyFunSuite with BeforeAndAfterEach with Checkers with AppendedClues with Matchers {
  private var simplifier: ConstSimplifier = _

  private val gens = new IrGenerators {
    override val maxArgs: Int = 3
  }
  private val ops =
    gens.simpleOperators ++ gens.logicOperators ++ gens.arithOperators ++ gens.setOperators ++ gens.functionOperators
  private val twoExpressions = for {
    e1 <- gens.genTlaEx(ops)(gens.emptyContext)
    e2 <- gens.genTlaEx(ops)(gens.emptyContext)
  } yield (e1, e2)

  private def nonemptySetGen(k: Int): Gen[TlaEx] = for {
    n <- Gen.choose(1, k)
    s <- Gen.pick(n, 0 until k).map(_.toSeq) // Converting generated Seq[Int] to an immutable Seq
    literalNonEmpty = tla.enumSet(s.map { i => tla.int(i) }: _*)
    symbolic = tla.name("S", SetT1(IntT1()))
    v <- Gen.oneOf(literalNonEmpty, symbolic)
  } yield v

  override def beforeEach(): Unit = {
    simplifier = new ConstSimplifier(new IdleTracker())
  }

  test("simplifies arithmetical operations with their neutral values") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(IntT1())))
      val expressions = List(
          tla.plus(tla.int(0), ex),
          tla.plus(ex, tla.int(0)),
          tla.minus(ex, tla.int(0)),
          tla.mult(ex, tla.int(1)),
          tla.mult(tla.int(1), ex),
          tla.div(ex, tla.int(1)),
          tla.exp(ex, tla.int(1)),
          // A more complex case to ensure recursion works properly: ex + (x - x)
          tla.plus(ex, tla.minus(tla.name("x", IntT1()), tla.name("x", IntT1()))),
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          (result shouldBe simplifier.simplify(ex)).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies arithmetical operations that result in 0") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(IntT1())))
      val expressions = List(
          tla.minus(ex, ex),
          tla.mult(ex, tla.int(0)),
          tla.mult(tla.int(0), ex),
          tla.div(tla.int(0), ex),
          tla.mod(ex, tla.int(1)),
          tla.mod(ex, ex),
      )

      // 0 ^ ex should not be 0 only when ex == 0
      try {
        if (simplifier.simplify(ex) != build(tla.int(0))) {
          expressions :+ tla.exp(tla.int(0), ex)
        }
      } catch {
        case _: TlaInputError =>
      }

      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          (result shouldBe build(tla.int(0))).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies arithmetical operations that result in 1") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(IntT1())))
      val expressions = List(
          tla.div(ex, ex),
          tla.exp(tla.int(1), ex),
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          (result shouldBe build(tla.int(1))).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies sums") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.plus(tla.int(a), tla.int(b))
      val result = simplifier.simplify(expression)

      (result shouldBe build(tla.int(a + b))).withClue(s"when simplifying ${expression.toString}")
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies subtractions") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.minus(tla.int(a), tla.int(b))
      val result = simplifier.simplify(expression)

      (result shouldBe build(tla.int(a - b))).withClue(s"when simplifying ${expression.toString}")
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies multiplications") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.mult(tla.int(a), tla.int(b))
      val result = simplifier.simplify(expression)

      (result shouldBe build(tla.int(a * b))).withClue(s"when simplifying ${expression.toString}")
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies divisions or throws error when invalid") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.div(tla.int(a), tla.int(b))

      if (b == 0) {
        val thrown = intercept[TlaInputError] {
          simplifier.simplify(expression)
        }

        (thrown.getMessage should startWith("Division by zero at")).withClue(s"when simplifying ${expression.toString}")
        true
      } else {
        val result = simplifier.simplify(expression)

        (result shouldBe build(tla.int(a / b))).withClue(s"when simplifying ${expression.toString}")
        true
      }
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies mods or throws error when invalid") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.mod(tla.int(a), tla.int(b))

      if (b == 0) {
        val thrown = intercept[TlaInputError] {
          simplifier.simplify(expression)
        }

        (thrown.getMessage should startWith("Mod by zero at")).withClue(s"when simplifying ${expression.toString}")
        true
      } else {
        val result = simplifier.simplify(expression)

        result shouldBe build(tla.int(a % b))
        true
      }
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  // Since exponential operators are highly value dependent due to precision and sizes, let's use unit tests
  test("simplifies expoents when values are usual") {
    val base: BigInt = Int.MaxValue * 2
    val power: Int = 10
    val expression = tla.exp(tla.int(base), tla.int(power))
    val result = simplifier.simplify(expression)

    (result shouldBe build(tla.int(base.pow(power)))).withClue(s"when simplifying ${expression.toString}")
  }

  test("raises error when power is too big") {
    val base: BigInt = 8888888
    val power: BigInt = BigInt(Int.MaxValue) + 1000
    val expression = tla.exp(tla.int(base), tla.int(power))
    val thrown = intercept[TlaInputError] {
      simplifier.simplify(expression)
    }

    thrown.getMessage shouldBe "The power at 8888888 ^ 2147484647 exceedes the limit of 2147483647"
  }

  test("raises error when result would be too big") {
    val base: Int = 2147483647
    val power: Int = 2103446789
    val expression = tla.exp(tla.int(base), tla.int(power))
    val thrown = intercept[TlaInputError] {
      simplifier.simplify(expression)
    }

    thrown.getMessage shouldBe "The result of 2147483647 ^ 2103446789 exceedes the limit of 1.7976931348623157E308"
  }

  test("simplifies logical expressions that result in TRUE") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(BoolT1())))
      val expressions = List(
          tla.eql(ex, ex),
          tla.or(ex, tla.bool(true)),
          tla.impl(ex, tla.bool(true)),
          tla.impl(tla.bool(false), ex),
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          (result shouldBe build(tla.bool(true))).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies logical expressions that result in FALSE") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(BoolT1())))
      val expressions = List(
          tla.neql(ex, ex),
          tla.and(ex, tla.bool(false)),
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          (result shouldBe build(tla.bool(false))).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  // TODO: remove and revisit tests below once all builder methods are implemented
  import TypedPredefs._
  import scala.language.implicitConversions
  implicit def builderBridge(bi: TBuilderInstruction): BuilderTlaExWrapper =
    BuilderTlaExWrapper(build(bi))

  test("simplifies logical expressions that result in part of the expression") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(BoolT1())))
      val expressions: List[TlaEx] = List(
          tla.and(ex),
          tla.and(ex, tla.bool(true)),
          tla.or(ex),
          tla.or(ex, tla.bool(false)),
          oldTla.ite(tla.bool(true), plainEx, tla.bool(false)).as(BoolT1()),
          oldTla.ite(tla.bool(false), tla.bool(false), plainEx).as(BoolT1()),
          oldTla.ite(plainEx, tla.bool(true), tla.bool(false)).as(BoolT1()),
          oldTla.ite(plainEx, ex, ex).as(BoolT1()),
          tla.not(tla.not(ex)),
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          (result shouldBe simplifier.simplify(ex)).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies logical expressions that result in part of the expression negated") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { plainEx =>
      val ex = tla.useTrustedEx(plainEx.withTag(Typed(BoolT1())))
      val expressions: List[TlaEx] = List(
          tla.impl(ex, tla.bool(false)),
          oldTla.ite(ex, tla.bool(false), tla.bool(true)).as(BoolT1()),
      )

      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          val negatedEx = tla.not(ex)
          (result shouldBe simplifier.simplify(negatedEx)).withClue(s"when simplifying ${expression.toString}")
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("evaluates relational expressions over constants") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      var trueExpressions: Seq[TlaEx] = Seq()
      var falseExpressions: Seq[TlaEx] = Seq()

      if (a < b) {
        trueExpressions = Seq(
            tla.lt(tla.int(a), tla.int(b)),
            tla.le(tla.int(a), tla.int(b)),
            tla.neql(tla.int(a), tla.int(b)),
        )

        falseExpressions = Seq(
            tla.eql(tla.int(a), tla.int(b)),
            tla.gt(tla.int(a), tla.int(b)),
            tla.ge(tla.int(a), tla.int(b)),
        )
      } else if (a > b) {
        trueExpressions = Seq(
            tla.gt(tla.int(a), tla.int(b)),
            tla.ge(tla.int(a), tla.int(b)),
            tla.neql(tla.int(a), tla.int(b)),
        )

        falseExpressions = Seq(
            tla.eql(tla.int(a), tla.int(b)),
            tla.lt(tla.int(a), tla.int(b)),
            tla.le(tla.int(a), tla.int(b)),
        )
      } else {
        trueExpressions = Seq(
            tla.ge(tla.int(a), tla.int(b)),
            tla.le(tla.int(a), tla.int(b)),
            tla.eql(tla.int(a), tla.int(b)),
        )

        falseExpressions = Seq(
            tla.neql(tla.int(a), tla.int(b)),
            tla.lt(tla.int(a), tla.int(b)),
            tla.gt(tla.int(a), tla.int(b)),
        )
      }

      trueExpressions.forall({ expression =>
        val result = simplifier.simplify(expression)

        (result shouldBe build(tla.bool(true))).withClue(s"when simplifying ${expression.toString}")
        true
      })

      falseExpressions.forall({ expression =>
        val result = simplifier.simplify(expression)

        (result shouldBe build(tla.bool(false))).withClue(s"when simplifying ${expression.toString}")
        true
      })
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies equality between strings") {
    val prop = forAll { (a: String, b: String) =>
      val eqlExpression = tla.eql(tla.str(a), tla.str(b))
      val eqlResult = simplifier.simplify(eqlExpression)

      val neqlExpression = tla.neql(tla.str(a), tla.str(b))
      val neqlResult = simplifier.simplify(neqlExpression)

      if (a == b) {
        (eqlResult shouldBe build(tla.bool(true))).withClue(s"when simplifying ${eqlExpression.toString}")
        (neqlResult shouldBe build(tla.bool(false))).withClue(s"when simplifying ${neqlExpression.toString}")
      } else {
        (eqlResult shouldBe build(tla.bool(false))).withClue(s"when simplifying ${eqlExpression.toString}")
        (neqlResult shouldBe build(tla.bool(true))).withClue(s"when simplifying ${neqlExpression.toString}")
      }
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies quantifiers which rewrite to Boolean constants") {
    val prop = forAll(gens.genType1) { t: TlaType1 =>
      def n_x = tla.name("x", t)
      def n_S = tla.name("S", SetT1(t))
      def n_p = tla.name("p", BoolT1())

      def emptySet = tla.emptySet(t)

      // \E x \in {}: P
      val existsEmpty = tla.exists(n_x, emptySet, n_p)
      val existsEmptyResult = simplifier.simplify(existsEmpty)
      // \A x \in {}: P
      val forallEmpty = tla.forall(n_x, emptySet, n_p)
      val forallEmptyResult = simplifier.simplify(forallEmpty)
      // \E x \in S: FALSE
      val existsFalse = tla.exists(n_x, n_S, tla.bool(false))
      val existsFalseResult = simplifier.simplify(existsFalse)
      // \A x \in S: TRUE
      val forallTrue = tla.forall(n_x, n_S, tla.bool(true))
      val forallTrueResult = simplifier.simplify(forallTrue)

      (existsEmptyResult shouldBe build(tla.bool(false))).withClue(s"when simplifying ${existsEmpty.toString}")
      (forallEmptyResult shouldBe build(tla.bool(true))).withClue(s"when simplifying ${forallEmpty.toString}")
      (existsFalseResult shouldBe build(tla.bool(false))).withClue(s"when simplifying ${existsFalse.toString}")
      (forallTrueResult shouldBe build(tla.bool(true))).withClue(s"when simplifying ${forallTrue.toString}")
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies quantifiers which rewrite to set emptiness checks") {
    val prop = forAll(nonemptySetGen(10)) { plainSetEx =>
      val setEx = tla.useTrustedEx(plainSetEx.withTag(Typed(SetT1(IntT1()))))
      def n_x = tla.name("x", IntT1())

      def emptySet = tla.emptySet(IntT1())

      // \E x \in S: TRUE
      val existsTrue = tla.exists(n_x, setEx, tla.bool(true))
      val existsTrueResult = simplifier.simplify(existsTrue)
      // \A x \in S: FALSE
      val forallFalse = tla.forall(n_x, setEx, tla.bool(false))
      val forallFalseResult = simplifier.simplify(forallFalse)

      def eql = tla.eql(setEx, emptySet)

      (existsTrueResult shouldBe build(tla.not(eql))).withClue(s"when simplifying ${existsTrue.toString}")
      (forallFalseResult shouldBe build(eql)).withClue(s"when simplifying ${forallFalse.toString}")

      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("evaluates logical expressions over constants") {
    val trueExpressions: Seq[TlaEx] = Seq(
        tla.not(tla.bool(false)),
        tla.impl(tla.bool(false), tla.bool(true)),
        tla.impl(tla.bool(false), tla.bool(false)),
        tla.impl(tla.bool(true), tla.bool(true)),
        tla.and(tla.bool(true)),
        tla.and(),
    )

    val falseExpressions: Seq[TlaEx] = Seq(
        tla.not(tla.bool(true)),
        tla.impl(tla.bool(true), tla.bool(false)),
        tla.or(tla.bool(false)),
        tla.or(),
    )

    trueExpressions.forall({ expression =>
      val result = simplifier.simplify(expression)

      (result shouldBe build(tla.bool(true))).withClue(s"when simplifying ${expression.toString}")
      true
    })

    falseExpressions.forall({ expression =>
      val result = simplifier.simplify(expression)

      (result shouldBe build(tla.bool(false))).withClue(s"when simplifying ${expression.toString}")
      true
    })
  }

  test("simplifies operations over multiple expressions") {
    val prop = forAll(twoExpressions) { case (plainE1, plainE2) =>
      val e1 = tla.useTrustedEx(plainE1.withTag(Typed(BoolT1())))
      val e2 = tla.useTrustedEx(plainE2.withTag(Typed(BoolT1())))
      val e2Set = tla.useTrustedEx(plainE2.withTag(Typed(SetT1(BoolT1()))))
      val expectations: Map[TlaEx, TlaEx] = List[(TlaEx, TlaEx)](
          // x /= y = !(x = y)
          (tla.neql(e1, e2), tla.not(tla.eql(e1, e2))),
          // !(x /= y) = x = y
          (tla.not(tla.neql(e1, e2)), tla.eql(e1, e2)),
          // TRUE /\ x /\ y = x /\ y
          (tla.and(tla.bool(true), e1, e2), tla.and(e1, e2)),
          // FALSE \/ x \/ y = x \/ y
          (tla.or(tla.bool(false), e1, e2), tla.or(e1, e2)),
          // IF x THEN FALSE ELSE y = !x /\ y
          (oldTla.ite(e1, tla.bool(false), e2).as(BoolT1()), tla.and(tla.not(e1), e2)),
          // IF x THEN TRUE ELSE y = x \/ y
          (oldTla.ite(e1, tla.bool(true), e2).as(BoolT1()), tla.or(e1, e2)),
          // x \notin y = !(x \in y)
          (tla.notin(e1, e2Set), tla.not(tla.in(e1, e2Set))),
          // !(x \notin y) = x \in y
          (tla.not(tla.notin(e1, e2Set)), tla.in(e1, e2Set)),
      ).toMap

      expectations.forall { case (expression, expectedSimplification) =>
        try {
          val result = simplifier.simplify(expression)
          (result shouldBe simplifier.simplify(expectedSimplification)).withClue(
              s"when simplifying ${expression.toString}")

          true
        } catch {
          case _: TlaInputError => true
        }
      }
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

}

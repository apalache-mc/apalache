package at.forsyte.apalache.tla.pp

import org.junit.runner.RunWith
import org.scalacheck.Prop.{AnyOperators, forAll, passed}
import org.scalacheck.Properties
import org.scalacheck.Gen
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers
import org.scalatest.{AppendedClues, Matchers}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{IntT1, BoolT1}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.typecheck._

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker

/**
 * Tests for ConstSimplifier.
 */
@RunWith(classOf[JUnitRunner])
class TestConstSimplifier extends FunSuite with BeforeAndAfterEach with Checkers with AppendedClues with Matchers {
  private var simplifier: ConstSimplifier = _

  private val gens = new IrGenerators {
    override val maxArgs: Int = 3
  }
  private val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
  private val twoExpressions = for {
    e1 <- gens.genTlaEx(ops)(gens.emptyContext)
    e2 <- gens.genTlaEx(ops)(gens.emptyContext)
  } yield (e1, e2)

  override def beforeEach(): Unit = {
    simplifier = new ConstSimplifier(new IdleTracker())
  }

  test("simplifies arithmetical operations with their neutral values") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.plus(tla.int(0), ex) as IntT1(),
          tla.plus(ex, tla.int(0)) as IntT1(),
          tla.minus(ex, tla.int(0)) as IntT1(),
          tla.mult(ex, tla.int(1)) as IntT1(),
          tla.mult(tla.int(1), ex) as IntT1(),
          tla.div(ex, tla.int(1)) as IntT1(),
          tla.exp(ex, tla.int(1)) as IntT1(),
          // A more complex case to ensure recursion works properly: ex + (x - x)
          tla.plus(ex, tla.minus(tla.name("x") as IntT1(), tla.name("x") as IntT1()) as IntT1()) as IntT1()
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          result shouldBe simplifier.simplify(ex) withClue s"when simplifying ${expression.toString}"
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies arithmetical operations that result in 0") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.minus(ex, ex) as IntT1(),
          tla.mult(ex, tla.int(0)) as IntT1(),
          tla.mult(tla.int(0), ex) as IntT1(),
          tla.div(tla.int(0), ex) as IntT1(),
          tla.mod(ex, tla.int(1)) as IntT1(),
          tla.mod(ex, ex) as IntT1()
      )

      // 0 ^ ex should not be 0 only when ex == 0
      try {
        if (simplifier.simplify(ex) != (tla.int(0) as IntT1())) {
          expressions :+ (tla.exp(tla.int(0), ex) as IntT1())
        }
      } catch {
        case _: TlaInputError =>
      }

      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          result shouldBe (tla.int(0) as IntT1()) withClue s"when simplifying ${expression.toString}"
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies arithmetical operations that result in 1") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.div(ex, ex) as IntT1(),
          tla.exp(tla.int(1), ex) as IntT1()
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          result shouldBe (tla.int(1) as IntT1()) withClue s"when simplifying ${expression.toString}"
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
      val expression = tla.plus(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result shouldBe (tla.int(a + b) as IntT1()) withClue s"when simplifying ${expression.toString}"
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies subtractions") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.minus(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result shouldBe (tla.int(a - b) as IntT1()) withClue s"when simplifying ${expression.toString}"
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies multiplications") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.mult(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result shouldBe (tla.int(a * b) as IntT1()) withClue s"when simplifying ${expression.toString}"
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies divisions or throws error when invalid") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.div(tla.int(a), tla.int(b)) as IntT1()

      if (b == 0) {
        val thrown = intercept[TlaInputError] {
          simplifier.simplify(expression)
        }

        thrown.getMessage should startWith("Division by zero at") withClue s"when simplifying ${expression.toString}"
        true
      } else {
        val result = simplifier.simplify(expression)

        result shouldBe (tla.int(a / b) as IntT1()) withClue s"when simplifying ${expression.toString}"
        true
      }
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies mods or throws error when invalid") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.mod(tla.int(a), tla.int(b)) as IntT1()

      if (b == 0) {
        val thrown = intercept[TlaInputError] {
          simplifier.simplify(expression)
        }

        thrown.getMessage should startWith("Mod by zero at") withClue s"when simplifying ${expression.toString}"
        true
      } else {
        val result = simplifier.simplify(expression)

        result shouldBe (tla.int(a % b) as IntT1())
        true
      }
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  // Since exponential operators are highly value dependent due to precision and sizes, let's use unit tests
  test("simplifies expoents when values are usual") {
    val base: BigInt = Int.MaxValue * 2
    val power: Int = 10
    val expression = tla.exp(tla.int(base), tla.int(power)) as IntT1()
    val result = simplifier.simplify(expression)

    result shouldBe (tla.int(base.pow(power)) as IntT1()) withClue s"when simplifying ${expression.toString}"
  }

  test("raises error when power is too big") {
    val base: BigInt = 8888888
    val power: BigInt = BigInt(Int.MaxValue) + 1000
    val expression = tla.exp(tla.int(base), tla.int(power)) as IntT1()
    val thrown = intercept[TlaInputError] {
      simplifier.simplify(expression)
    }

    thrown.getMessage shouldBe ("The power at 8888888 ^ 2147484647 exceedes the limit of 2147483647")
  }

  test("raises error when result would be too big") {
    val base: Int = 2147483647
    val power: Int = 2103446789
    val expression = tla.exp(tla.int(base), tla.int(power)) as IntT1()
    val thrown = intercept[TlaInputError] {
      simplifier.simplify(expression)
    }

    thrown.getMessage shouldBe ("The result of 2147483647 ^ 2103446789 exceedes the limit of 1.7976931348623157E308")
  }

  test("simplifies logical expressions that result in TRUE") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.eql(ex, ex) as BoolT1(),
          tla.or(ex, tla.bool(true) as BoolT1()) as BoolT1(),
          tla.impl(ex, tla.bool(true) as BoolT1()) as BoolT1(),
          tla.impl(tla.bool(false) as BoolT1(), ex) as BoolT1()
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          result shouldBe (tla.bool(true) as BoolT1()) withClue s"when simplifying ${expression.toString}"
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies logical expressions that result in FALSE") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.neql(ex, ex) as BoolT1(),
          tla.and(ex, tla.bool(false) as BoolT1()) as BoolT1()
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          result shouldBe (tla.bool(false) as BoolT1()) withClue s"when simplifying ${expression.toString}"
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies logical expressions that result in part of the expression") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.and(ex) as BoolT1(),
          tla.and(ex, tla.bool(true) as BoolT1()) as BoolT1(),
          tla.or(ex) as BoolT1(),
          tla.or(ex, tla.bool(false) as BoolT1()) as BoolT1(),
          tla.ite(tla.bool(true) as BoolT1(), ex, tla.bool(false) as BoolT1()) as BoolT1(),
          tla.ite(tla.bool(false) as BoolT1(), tla.bool(false) as BoolT1(), ex) as BoolT1(),
          tla.ite(ex, tla.bool(true) as BoolT1(), tla.bool(false) as BoolT1()) as BoolT1(),
          tla.ite(ex, ex, ex) as BoolT1(),
          tla.not(tla.not(ex) as BoolT1()) as BoolT1()
      )
      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          result shouldBe simplifier.simplify(ex) withClue s"when simplifying ${expression.toString}"
          true
        } catch {
          case _: TlaInputError => true
        }
      })

    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies logical expressions that result in part of the expression negated") {
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List(
          tla.impl(ex, tla.bool(false) as BoolT1()) as BoolT1(),
          tla.ite(ex, tla.bool(false) as BoolT1(), tla.bool(true) as BoolT1()) as BoolT1()
      )

      expressions.forall({ expression =>
        try {
          val result = simplifier.simplify(expression)

          val negatedEx = tla.not(ex) as BoolT1()
          result shouldBe simplifier.simplify(negatedEx) withClue s"when simplifying ${expression.toString}"
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
            tla.lt(tla.int(a), tla.int(b)) as BoolT1(),
            tla.le(tla.int(a), tla.int(b)) as BoolT1(),
            tla.neql(tla.int(a), tla.int(b)) as BoolT1()
        )

        falseExpressions = Seq(
            tla.eql(tla.int(a), tla.int(b)) as BoolT1(),
            tla.gt(tla.int(a), tla.int(b)) as BoolT1(),
            tla.ge(tla.int(a), tla.int(b)) as BoolT1()
        )
      } else if (a > b) {
        trueExpressions = Seq(
            tla.gt(tla.int(a), tla.int(b)) as BoolT1(),
            tla.ge(tla.int(a), tla.int(b)) as BoolT1(),
            tla.neql(tla.int(a), tla.int(b)) as BoolT1()
        )

        falseExpressions = Seq(
            tla.eql(tla.int(a), tla.int(b)) as BoolT1(),
            tla.lt(tla.int(a), tla.int(b)) as BoolT1(),
            tla.le(tla.int(a), tla.int(b)) as BoolT1()
        )
      } else {
        trueExpressions = Seq(
            tla.ge(tla.int(a), tla.int(b)) as BoolT1(),
            tla.le(tla.int(a), tla.int(b)) as BoolT1(),
            tla.eql(tla.int(a), tla.int(b)) as BoolT1()
        )

        falseExpressions = Seq(
            tla.neql(tla.int(a), tla.int(b)) as BoolT1(),
            tla.lt(tla.int(a), tla.int(b)) as BoolT1(),
            tla.gt(tla.int(a), tla.int(b)) as BoolT1()
        )
      }

      trueExpressions.forall({ expression =>
        val result = simplifier.simplify(expression)

        result shouldBe (tla.bool(true) as BoolT1()) withClue s"when simplifying ${expression.toString}"
        true
      })

      falseExpressions.forall({ expression =>
        val result = simplifier.simplify(expression)

        result shouldBe (tla.bool(false) as BoolT1()) withClue s"when simplifying ${expression.toString}"
        true
      })
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("simplifies equality between strings") {
    val prop = forAll { (a: String, b: String) =>
      val eqlExpression = tla.eql(tla.str(a), tla.str(b)) as BoolT1()
      val eqlResult = simplifier.simplify(eqlExpression)

      val neqlExpression = tla.neql(tla.str(a), tla.str(b)) as BoolT1()
      val neqlResult = simplifier.simplify(neqlExpression)

      if (a == b) {
        eqlResult shouldBe (tla.bool(true) as BoolT1()) withClue s"when simplifying ${eqlExpression.toString}"
        neqlResult shouldBe (tla.bool(false) as BoolT1()) withClue s"when simplifying ${neqlExpression.toString}"
      } else {
        eqlResult shouldBe (tla.bool(false) as BoolT1()) withClue s"when simplifying ${eqlExpression.toString}"
        neqlResult shouldBe (tla.bool(true) as BoolT1()) withClue s"when simplifying ${neqlExpression.toString}"
      }
      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("evaluates logical expressions over constants") {
    var trueExpressions: Seq[TlaEx] = Seq(
        tla.not(tla.bool(false)) as BoolT1(),
        tla.impl(tla.bool(false), tla.bool(true)) as BoolT1(),
        tla.impl(tla.bool(false), tla.bool(false)) as BoolT1(),
        tla.impl(tla.bool(true), tla.bool(true)) as BoolT1(),
        tla.and(tla.bool(true)) as BoolT1(),
        tla.and() as BoolT1()
    )

    var falseExpressions: Seq[TlaEx] = Seq(
        tla.not(tla.bool(true)) as BoolT1(),
        tla.impl(tla.bool(true), tla.bool(false)) as BoolT1(),
        tla.or(tla.bool(false)) as BoolT1(),
        tla.or() as BoolT1()
    )

    trueExpressions.forall({ expression =>
      val result = simplifier.simplify(expression)

      result shouldBe (tla.bool(true) as BoolT1()) withClue s"when simplifying ${expression.toString}"
      true
    })

    falseExpressions.forall({ expression =>
      val result = simplifier.simplify(expression)

      result shouldBe (tla.bool(false) as BoolT1()) withClue s"when simplifying ${expression.toString}"
      true
    })
  }

  test("simplifies operations over multiple expressions") {
    val prop = forAll(twoExpressions) { expressions =>
      expressions match {
        case (e1, e2) =>
          val expectations = Map(
              // x /= y = !(x = y)
              (tla.neql(e1, e2) as BoolT1()) -> (tla.not(tla.eql(e1, e2) as BoolT1()) as BoolT1()),
              // !(x /= y) = x = y
              (tla.not(tla.neql(e1, e2) as BoolT1()) as BoolT1()) -> (tla.eql(e1, e2) as BoolT1()),
              // TRUE /\ x /\ y = x /\ y
              (tla.and(tla.bool(true) as BoolT1(), e1, e2) as BoolT1()) -> (tla.and(e1, e2) as BoolT1()),
              // FALSE \/ x \/ y = x \/ y
              (tla.or(tla.bool(false) as BoolT1(), e1, e2) as BoolT1()) -> (tla.or(e1, e2) as BoolT1()),
              // IF x THEN FALSE ELSE y = !x /\ y
              (tla.ite(e1, tla.bool(false) as BoolT1(), e2) as BoolT1()) -> (tla.and(tla.not(e1) as BoolT1(),
                  e2) as BoolT1()),
              // IF x THEN TRUE ELSE y = x \/ y
              (tla.ite(e1, tla.bool(true) as BoolT1(), e2) as BoolT1()) -> (tla.or(e1, e2) as BoolT1()),
              // x \notin y = !(x \in y)
              (tla.notin(e1, e2) as BoolT1()) -> (tla.not(tla.in(e1, e2) as BoolT1()) as BoolT1()),
              // !(x \notin y) = x \in y
              (tla.not(tla.notin(e1, e2) as BoolT1()) as BoolT1()) -> (tla.in(e1, e2) as BoolT1())
          )

          expectations.forall { case (expression, expectedSimplification) =>
            try {
              val result = simplifier.simplify(expression)
              result shouldBe simplifier.simplify(
                  expectedSimplification) withClue s"when simplifying ${expression.toString}"

              true
            } catch {
              case _: TlaInputError => true
            }
          }
      }
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

}

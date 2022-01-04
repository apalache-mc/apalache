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
import at.forsyte.apalache.tla.lir.IntT1
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

  override def beforeEach(): Unit = {
    simplifier = new ConstSimplifier(new IdleTracker())
  }

  test("simplifies arithmetical operations with their neutral values") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
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
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
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
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
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
    val base: BigInt = 8888888
    val power: Int = 40
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

    thrown.getMessage shouldBe ("Power of 2147484647 is bigger than the max allowed of 64 at 8888888 ^ 2147484647")
  }
}

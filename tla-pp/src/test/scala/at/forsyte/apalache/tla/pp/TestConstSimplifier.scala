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
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.SetT1
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
      val expressions = List (
        tla.plus(tla.int(0), ex) as IntT1(),
        tla.plus(ex, tla.int(0)) as IntT1(),
        tla.minus(ex, tla.int(0)) as IntT1(),
        tla.mult(ex, tla.int(1)) as IntT1(),
        tla.mult(tla.int(1), ex) as IntT1(),
        tla.div(ex, tla.int(1)) as IntT1(),
        tla.exp(ex, tla.int(1)) as IntT1(),
        // A more complex case to ensure recursion works properly: ex + (x - x)
        tla.plus(ex, tla.minus(tla.name("x") as IntT1(), tla.name("x") as IntT1()) as IntT1()) as IntT1(),
      )
      expressions.forall({ expression =>
                           try {
                             val result = simplifier.simplify(expression)
                             val expected = simplifier.simplify(ex)
                             result shouldBe expected
                             true
                           } catch {
                             case _: IllegalArgumentException => true
                           }
                         })

    }
    check(prop, minSuccessful(2500), sizeRange(8))
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
        tla.mod(ex, ex) as IntT1(),
        // TODO: This should not be 0 only when ex = 0. Find a way to test it.
        // tla.exp(tla.int(0), ex) as IntT1(),
      )
      expressions.forall({ expression =>
                           try{
                             val result = simplifier.simplify(expression)
                             result shouldBe (ValEx(TlaInt(0))(Typed(IntT1()))) withClue s"${expression.toString} should be simplified to 0 but is instead ${result.toString}"
                             true
                           } catch {
                             case _: IllegalArgumentException => true
                           }
                         })

    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies arithmetical operations that result in 1") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      val expressions = List (
        tla.div(ex, ex) as IntT1(),
        tla.exp(tla.int(1), ex) as IntT1(),
      )
      expressions.forall({ expression =>
                           try{
                             val result = simplifier.simplify(expression)
                             result shouldBe (ValEx(TlaInt(1))(Typed(IntT1()))) withClue s"${expression.toString} should be simplified to 0 but is instead ${result.toString}"
                             true
                           } catch {
                             case _: IllegalArgumentException => true
                           }
                         })

    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies sums") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.plus(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == a + b
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies subtractions") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.minus(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == a - b
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies multiplications") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      val expression = tla.mult(tla.int(a), tla.int(b)) as IntT1()
      val result = simplifier.simplify(expression)

      result match {
        case ValEx(TlaInt(x)) =>
          x == a * b
        case _ =>
          false
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies divisions") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      if (b == 0) {
        true
      } else {
        val expression = tla.div(tla.int(a), tla.int(b)) as IntT1()
        val result = simplifier.simplify(expression)

        result match {
          case ValEx(TlaInt(x)) =>
            x == a / b
          case _ =>
            false
        }
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("simplifies mods") {
    val prop = forAll { (a: BigInt, b: BigInt) =>
      if (b == 0) {
        true
      } else {
        val expression = tla.mod(tla.int(a), tla.int(b)) as IntT1()
        val result = simplifier.simplify(expression)

        result match {
          case ValEx(TlaInt(x)) =>
            x == a % b
          case _ =>
            false
        }
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  // test("simplifies expoents") {
  //   val prop = forAll(posNum[BigInt]) { (a: BigInt, b: BigInt) =>
  //     val expression = tla.exp(tla.int(a), tla.int(b)) as IntT1()
  //     val result = simplifier.simplify(expression)

  //     result match {
  //       case ValEx(TlaInt(x)) =>
  //         x == a.pow(b.toInt)
  //       case _ =>
  //         false
  //     }
  //   }
  //   check(prop, minSuccessful(2), sizeRange(8))
  // }

}

package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalacheck.Prop.forAll
import org.scalacheck.{Gen, Prop}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestMockOracle extends AnyFunSuite with BeforeAndAfterEach with Checkers {

  var initScope: RewriterScope = RewriterScope.initial()

  override def beforeEach(): Unit = {
    initScope = RewriterScope.initial()
  }

  val intGen: Gen[Int] = Gen.choose(-10, 10)
  val nonNegIntGen: Gen[Int] = Gen.choose(0, 9)

  val maxSizeAndIndexGen: Gen[(Int, Int)] = for {
    max <- nonNegIntGen
    idx <- Gen.choose(0, max)
  } yield (max, idx)

  test("Oracle cannot be constructed with a negative fixed value") {
    val prop =
      forAll(intGen) {
        case i if i < 0 =>
          Prop.throws(classOf[IllegalArgumentException]) {
            MockOracle.create(i)
          }
        case i => MockOracle.create(i).size == i + 1
      }

    check(prop, minSuccessful(100), sizeRange(4))
  }

  test("chosenValueIsEqualToIndexedValue returns a simple boolean") {
    val prop =
      forAll(maxSizeAndIndexGen) { case (fixed, index) =>
        val oracle = MockOracle.create(fixed)
        val cmp: TlaEx = oracle.chosenValueIsEqualToIndexedValue(initScope, index)
        cmp match {
          case ValEx(TlaBool(v)) => v == (index == fixed)
          case _                 => false
        }
      }

    check(prop, minSuccessful(1000), sizeRange(4))
  }

  val (assertionsA, assertionsB): (Seq[TBuilderInstruction], Seq[TBuilderInstruction]) = 0
    .to(10)
    .map { i =>
      (tla.name(s"A$i", BoolT1), tla.name(s"B$i", BoolT1))
    }
    .unzip

  test("caseAssertions requires assertion sequences of equal length") {
    val assertionsGen: Gen[(Seq[TBuilderInstruction], Option[Seq[TBuilderInstruction]])] = for {
      i <- Gen.choose(0, assertionsA.size)
      j <- Gen.choose(0, assertionsB.size)
      opt <- Gen.option(Gen.const(assertionsB.take(j)))
    } yield (assertionsA.take(i), opt)

    val prop =
      forAll(Gen.zip(nonNegIntGen, assertionsGen)) { case (fixed, (assertionsIfTrue, assertionsIfFalseOpt)) =>
        val oracle = MockOracle.create(fixed)
        if (assertionsIfTrue.size != oracle.size || assertionsIfFalseOpt.exists { _.size != oracle.size })
          Prop.throws(classOf[IllegalArgumentException]) {
            oracle.caseAssertions(initScope, assertionsIfTrue, assertionsIfFalseOpt)
          }
        else true
      }

    check(prop, minSuccessful(1000), sizeRange(4))
  }

  test("caseAssertions always shorthands") {
    val gen: Gen[(Int, Seq[TBuilderInstruction], Option[Seq[TBuilderInstruction]])] = for {
      fixed <- nonNegIntGen
      opt <- Gen.option(Gen.const(assertionsB.take(fixed + 1)))
    } yield (fixed, assertionsA.take(fixed + 1), opt)

    val prop =
      forAll(gen) { case (fixed, assertionsIfTrue, assertionsIfFalseOpt) =>
        val oracle = MockOracle.create(fixed)
        val caseEx: TlaEx = oracle.caseAssertions(initScope, assertionsIfTrue, assertionsIfFalseOpt)
        caseEx == assertionsIfTrue(fixed).build
      }

    check(prop, minSuccessful(1000), sizeRange(4))
  }

  // We don't actually need the solver in MockOracle
  test("getIndexOfChosenValueFromModel recovers the index correctly") {
    val prop =
      forAll(Gen.zip(nonNegIntGen)) { fixed =>
        val ctx = new Z3SolverContext(SolverConfig.default)
        val oracle = MockOracle.create(fixed)
        oracle.getIndexOfChosenValueFromModel(ctx) == fixed
      }

    check(prop, minSuccessful(100), sizeRange(4))
  }
}

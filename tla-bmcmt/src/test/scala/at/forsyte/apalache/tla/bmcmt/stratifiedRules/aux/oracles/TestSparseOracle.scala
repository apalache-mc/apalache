package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestSparseOracle extends AnyFunSuite with BeforeAndAfterEach with Checkers {

  var initScope: RewriterScope = RewriterScope.initial()

  override def beforeEach(): Unit = {
    initScope = RewriterScope.initial()
  }

  val intGen: Gen[Int] = Gen.choose(-10, 10)
  val nonNegIntGen: Gen[Int] = Gen.choose(0, 10)

  val maxSizeAndSetGen: Gen[(Int, Set[Int])] = for {
    max <- nonNegIntGen
    elems <- Gen.listOfN(max, Gen.choose(0, max))
  } yield (max, elems.toSet)

  val maxSizeIndexAndSetGen: Gen[(Int, Int, Set[Int])] = for {
    max <- Gen.choose(1, 20) // we want size > 0
    elems <- Gen.listOfN(max, Gen.choose(0, max))
    set =
      if (elems.nonEmpty) elems.toSet
      else Set(0) // we don't want the degenerate case where set is empty, so we just pad it with 0
    idx <- Gen.choose(0, set.size - 1)
  } yield (max, idx, set)

  test("chosenValueIsEqualToIndexedValue forwards to the original oracle correctly") {
    val prop =
      forAll(Gen.zip(maxSizeAndSetGen, intGen)) { case ((size, set), index) =>
        val (scope, intOracle) = IntOracle.create(initScope, size)
        val oracle = new SparseOracle(intOracle, set)
        val cmp: TlaEx = oracle.chosenValueIsEqualToIndexedValue(scope, index)
        if (index < 0 || index >= oracle.size)
          cmp == tla.bool(false).build
        else {
          cmp == intOracle.chosenValueIsEqualToIndexedValue(scope, oracle.sortedValues(index)).build
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

  // "caseAssertions" tests ignored, since SparseOracle literally just invokes the underlying oracle's method,
  // which should have its own tests

  // TODO: Enable test after #2743
  // We cannot test getIndexOfChosenValueFromModel without running the solver
  ignore("getIndexOfChosenValueFromModel recovers the index correctly") {
    val prop =
      forAll(maxSizeIndexAndSetGen) { case (size, index, set) =>
        val ctx = new Z3SolverContext(SolverConfig.default)
        val paa = PureArenaAdapter.create(ctx) // We use PAA, since it performs the basic context initialization
        val (scope, intOracle) = IntOracle.create(initScope.copy(arena = paa.arena), size)
        ctx.declareCell(intOracle.intCell)
        val oracle = new SparseOracle(intOracle, set)
        val eql = oracle.chosenValueIsEqualToIndexedValue(scope, index)
        ctx.assertGroundExpr(eql)
        ctx.sat()
        oracle.getIndexOfChosenValueFromModel(ctx) == index
      }

    // 1000 is too many, since each run invokes the solver
    check(prop, minSuccessful(80), sizeRange(4))
  }
}

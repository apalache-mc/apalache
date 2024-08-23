package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, PureArena}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import at.forsyte.apalache.tla.typecomp._
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
  var intOracleCell: ArenaCell = PureArena.cellInvalid

  def mkIntOracle(n: Int): Oracle = new IntOracle(intOracleCell, n)

  override def beforeEach(): Unit = {
    val scope0 = RewriterScope.initial()
    initScope = scope0.copy(arena = scope0.arena.appendCell(CellT.fromType1(IntT1)))
    intOracleCell = initScope.arena.topCell
  }

  val intGen: Gen[Int] = Gen.choose(-10, 10)
  val nonNegIntGen: Gen[Int] = Gen.choose(0, 20)

  val setGen: Gen[Set[Int]] = for {
    maxSize <- nonNegIntGen
    elems <- Gen.listOfN(maxSize, nonNegIntGen)
  } yield elems.toSet

  val nonemptySetAndIdxGen: Gen[(Set[Int], Int)] = for {
    maxSize <- Gen.choose(1, 20)
    elems <- Gen.listOfN(maxSize, nonNegIntGen)
    idx <- Gen.oneOf(elems)
  } yield (elems.toSet, idx)

  test("chosenValueIsEqualToIndexedValue returns the correct value for any element of the constructor set") {
    val prop =
      forAll(Gen.zip(setGen, intGen)) { case (set, index) =>
        val oracle = new SparseOracle(mkIntOracle, set)
        val cmp: TlaEx = oracle.chosenValueIsEqualToIndexedValue(initScope, index)
        if (!set.contains(index))
          cmp == tla.bool(false).build
        else {
          cmp == oracle.oracle.chosenValueIsEqualToIndexedValue(initScope, oracle.indexMap(index)).build
        }
      }

    check(prop, minSuccessful(1000), sizeRange(4))
  }

  val (assertionsA, assertionsB): (Seq[BuilderT], Seq[BuilderT]) = 0
    .to(10)
    .map { i =>
      (tla.name(s"A$i", BoolT1), tla.name(s"B$i", BoolT1))
    }
    .unzip

  // "caseAssertions" tests ignored, since SparseOracle literally just invokes the underlying oracle's method,
  // which should have its own tests

  // We cannot test getIndexOfChosenValueFromModel without running the solver
  test("getIndexOfChosenValueFromModel recovers the index correctly") {
    val ctx = new Z3SolverContext(SolverConfig.default)
    val paa = PureArenaAdapter.create(ctx) // We use PAA, since it performs the basic context initialization
    val paa2 = paa.appendCell(IntT1) // also declares the cell
    intOracleCell = paa2.topCell
    initScope = initScope.copy(arena = paa2.arena)
    val prop =
      forAll(nonemptySetAndIdxGen) { case (set, index) =>
        val oracle = new SparseOracle(mkIntOracle, set)
        val eql = oracle.chosenValueIsEqualToIndexedValue(initScope, index)
        ctx.push()
        ctx.assertGroundExpr(eql)
        ctx.sat()
        val ret = oracle.getIndexOfChosenValueFromModel(ctx) == index
        ctx.pop()
        ret
      }

    // The default minimum successful runs is 1000, but this is costly
    // since each run invokes the solver.
    check(prop, minSuccessful(50), sizeRange(4))
  }
}

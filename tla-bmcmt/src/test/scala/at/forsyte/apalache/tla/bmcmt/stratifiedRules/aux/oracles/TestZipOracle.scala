package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.values.TlaBool
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestZipOracle extends AnyFunSuite with BeforeAndAfterEach with Checkers {

  var (initScope, backOracle): (RewriterScope, Oracle) = IntOracle.create(RewriterScope.initial(), 12)

  override def beforeEach(): Unit = {
    val pa = IntOracle.create(RewriterScope.initial(), 12)
    initScope = pa._1
    backOracle = pa._2
  }

  val intGen: Gen[Int] = Gen.choose(-10, 10)
  val nonNegIntGen: Gen[Int] = Gen.choose(0, 10)

  val groupGen: Gen[Seq[Seq[Int]]] = for {
    nGroups <- Gen.oneOf(0, 1, 2, 3, 4, 6, 12)
  } yield
    if (nGroups == 0) Seq.empty
    else 0.until(12).grouped(nGroups).map(_.toSeq).toSeq

  test("chosenValueIsEqualToIndexedValue returns an OR or FALSE") {
    val prop =
      forAll(Gen.zip(groupGen, nonNegIntGen)) { case (groups, index) =>
        val oracle = new ZipOracle(backOracle, groups)
        val cmp: TlaEx = oracle.chosenValueIsEqualToIndexedValue(initScope, index)
        cmp match {
          case ValEx(TlaBool(false))             => !groups.indices.contains(index)
          case OperEx(TlaBoolOper.or, args @ _*) => groups.indices.contains(index) && (args.length * groups.size == 12)
          case _                                 => false
        }
      }

    check(prop, minSuccessful(1000), sizeRange(4))
  }

  // Redundant, since the base method is tested already
  // test("caseAssertions requires assertion sequences of equal length") { ... }
  // test("caseAssertions constructs a collection of ITEs, or shorthands") { ... }

  // We cannot test getIndexOfChosenValueFromModel without running the solver
  // Ignored until we figure out why it's killing GH CLI
  ignore("getIndexOfChosenValueFromModel recovers the index correctly") {
    val prop =
      forAll(Gen.zip(groupGen, Gen.choose(0, 11))) { case (groups, idx) =>
        val ctx = new Z3SolverContext(SolverConfig.default)
        val paa = PureArenaAdapter.create(ctx) // We use PAA, since it performs the basic context initialization
        val (scope, backOracle) = IntOracle.create(RewriterScope.initial().copy(arena = paa.arena), 12)
        val oracle = new ZipOracle(backOracle, groups)
        ctx.declareCell(backOracle.intCell)

        val eql = backOracle.chosenValueIsEqualToIndexedValue(scope, idx)
        ctx.assertGroundExpr(eql)
        ctx.sat()
        oracle.getIndexOfChosenValueFromModel(ctx) == groups.indexWhere(_.contains(idx))
      }

    // 1000 is too many, since each run invokes the solver
    check(prop, minSuccessful(80), sizeRange(4))
  }
}

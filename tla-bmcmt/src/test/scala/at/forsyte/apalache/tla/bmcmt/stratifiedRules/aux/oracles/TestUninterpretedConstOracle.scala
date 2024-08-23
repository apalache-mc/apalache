package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.UninterpretedLiteralCache
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{Rewriter, RewriterScope, TestingRewriter}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import at.forsyte.apalache.tla.typecomp._
import org.junit.runner.RunWith
import org.scalacheck.Prop.forAll
import org.scalacheck.{Gen, Prop}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestUninterpretedConstOracle extends AnyFunSuite with BeforeAndAfterEach with Checkers {

  var rewriter: Rewriter = TestingRewriter(Map.empty)
  var cache: UninterpretedLiteralCache = new UninterpretedLiteralCache
  var initScope: RewriterScope = RewriterScope.initial()

  override def beforeEach(): Unit = {
    rewriter = TestingRewriter(Map.empty)
    cache = new UninterpretedLiteralCache
    initScope = RewriterScope.initial()
  }

  val intGen: Gen[Int] = Gen.choose(-10, 10)
  val nonNegIntGen: Gen[Int] = Gen.choose(0, 10)

  val maxSizeAndIndexGen: Gen[(Int, Int)] = for {
    max <- Gen.choose(1, 10) // size 0 is degenerate
    idx <- Gen.choose(0, max - 1) // index must be <
  } yield (max, idx)

  test("Oracle cannot be constructed with negative size") {
    val prop =
      forAll(intGen) {
        case i if i < 0 =>
          Prop.throws(classOf[IllegalArgumentException]) {
            UninterpretedConstOracle.create(rewriter, cache, initScope, i)
          }
        case i => UninterpretedConstOracle.create(rewriter, cache, initScope, i)._2.size == i
      }

    check(prop, minSuccessful(100), sizeRange(4))
  }

  test("chosenValueIsEqualToIndexedValue returns an equality, or shorthands") {
    val prop =
      forAll(Gen.zip(nonNegIntGen, intGen)) { case (size, index) =>
        val (scope, oracle) = UninterpretedConstOracle.create(rewriter, cache, initScope, size)
        val cmp: TlaEx = oracle.chosenValueIsEqualToIndexedValue(scope, index)
        if (index < 0 || index >= size)
          cmp == tla.bool(false).build
        else
          cmp match {
            case OperEx(TlaOper.eq, NameEx(name1), NameEx(name2)) =>
              name1 == oracle.oracleCell.toString && name2 == oracle.valueCells(index).toString
            case _ => false
          }
      }

    check(prop, minSuccessful(200), sizeRange(4))
  }

  val (assertionsA, assertionsB): (Seq[BuilderT], Seq[BuilderT]) = 0
    .to(10)
    .map { i =>
      (tla.name(s"A$i", BoolT1), tla.name(s"B$i", BoolT1))
    }
    .unzip

  test("caseAssertions requires assertion sequences of equal length") {
    val assertionsGen: Gen[(Seq[BuilderT], Option[Seq[BuilderT]])] = for {
      i <- Gen.choose(0, assertionsA.size)
      j <- Gen.choose(0, assertionsB.size)
      opt <- Gen.option(Gen.const(assertionsB.take(j)))
    } yield (assertionsA.take(i), opt)

    val prop =
      forAll(Gen.zip(nonNegIntGen, assertionsGen)) { case (size, (assertionsIfTrue, assertionsIfFalseOpt)) =>
        val (scope, oracle) = UninterpretedConstOracle.create(rewriter, cache, initScope, size)
        if (assertionsIfTrue.size != oracle.size || assertionsIfFalseOpt.exists { _.size != oracle.size })
          Prop.throws(classOf[IllegalArgumentException]) {
            oracle.caseAssertions(scope, assertionsIfTrue, assertionsIfFalseOpt)
          }
        else true
      }

    check(prop, minSuccessful(200), sizeRange(4))
  }

  test("caseAssertions constructs a collection of ITEs, or shorthands") {
    val gen: Gen[(Int, Seq[BuilderT], Option[Seq[BuilderT]])] = for {
      size <- nonNegIntGen
      opt <- Gen.option(Gen.const(assertionsB.take(size)))
    } yield (size, assertionsA.take(size), opt)

    val prop =
      forAll(gen) { case (size, assertionsIfTrue, assertionsIfFalseOpt) =>
        val (scope, oracle) = UninterpretedConstOracle.create(rewriter, cache, initScope, size)
        val caseEx: TlaEx = oracle.caseAssertions(scope, assertionsIfTrue, assertionsIfFalseOpt)
        size match {
          case 0 =>
            caseEx == PureArena.cellTrue(scope.arena).toBuilder.build
          case 1 =>
            caseEx == assertionsA.head.build
          case _ =>
            assertionsIfFalseOpt match {
              case None =>
                val ites = assertionsIfTrue.zip(oracle.valueCells).map { case (a, c) =>
                  tla.ite(tla.eql(oracle.oracleCell.toBuilder, c.toBuilder), a, tla.bool(true))
                }
                caseEx == tla.and(ites: _*).build
              case Some(assertionsIfFalse) =>
                val ites = assertionsIfTrue.zip(assertionsIfFalse).zip(oracle.valueCells).map { case ((at, af), c) =>
                  tla.ite(tla.eql(oracle.oracleCell.toBuilder, c.toBuilder), at, af)
                }
                caseEx == tla.and(ites: _*).build
            }
        }
      }

    check(prop, minSuccessful(200), sizeRange(4))
  }

  // We cannot test getIndexOfChosenValueFromModel without running the solver
  // Ignored until we figure out why it's killing GH CLI
  ignore("getIndexOfChosenValueFromModel recovers the index correctly for nonempty cell collection") {
    val ctx = new Z3SolverContext(SolverConfig.default)
    val paa = PureArenaAdapter.create(ctx) // We use PAA, since it performs the basic context initialization
    initScope = initScope.copy(arena = paa.arena)
    val prop =
      forAll(maxSizeAndIndexGen) { case (size, index) =>
        cache.dispose() // prevent redeclarations in every loop
        val (scope, oracle) = UninterpretedConstOracle.create(rewriter, cache, initScope, size)
        ctx.push()
        oracle.valueCells.foreach(ctx.declareCell)
        ctx.declareCell(oracle.oracleCell)
        cache.addAllConstraints(ctx)
        val eql = oracle.chosenValueIsEqualToIndexedValue(scope, index)
        ctx.assertGroundExpr(eql)
        ctx.sat()
        val ret = oracle.getIndexOfChosenValueFromModel(ctx) == index
        ctx.pop()
        ret
      }

    // 1000 is too many, since each run invokes the solver
    check(prop, minSuccessful(80), sizeRange(4))
  }

  test("getIndexOfChosenValueFromModel recovers the index correctly for empty collections") {
    val ctx = new Z3SolverContext(SolverConfig.default)
    val paa = PureArenaAdapter.create(ctx) // We use PAA, since it performs the basic context initialization
    val (_, oracle) = UninterpretedConstOracle.create(rewriter, cache, initScope.copy(arena = paa.arena), 0)
    ctx.declareCell(oracle.oracleCell)
    ctx.sat()
    assert(oracle.getIndexOfChosenValueFromModel(ctx) == -1)
  }

}

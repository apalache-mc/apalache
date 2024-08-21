package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.lir.{BoolT1, NameEx, OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import at.forsyte.apalache.tla.typecomp._
import org.junit.runner.RunWith
import org.scalacheck.{Gen, Prop}
import org.scalacheck.Prop.forAll
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestIntOracle extends AnyFunSuite with BeforeAndAfterEach with Checkers {

  var initScope: RewriterScope = RewriterScope.initial()

  override def beforeEach(): Unit = {
    initScope = RewriterScope.initial()
  }

  val intGen: Gen[Int] = Gen.choose(-10, 10)
  val nonNegIntGen: Gen[Int] = Gen.choose(0, 10)

  val maxSizeAndIndexGen: Gen[(Int, Int)] = for {
    max <- nonNegIntGen
    idx <- Gen.choose(0, max)
  } yield (max, idx)

  test("Oracle cannot be constructed with negative size") {
    val prop =
      forAll(intGen) {
        case i if i < 0 =>
          Prop.throws(classOf[IllegalArgumentException]) {
            IntOracle.create(initScope, i)
          }
        case i => IntOracle.create(initScope, i)._2.size == i
      }

    check(prop, minSuccessful(100), sizeRange(4))
  }

  test("chosenValueIsEqualToIndexedValue returns an integer comparison") {
    val prop =
      forAll(maxSizeAndIndexGen) { case (size, index) =>
        val (scope, oracle) = IntOracle.create(initScope, size)
        val cmp: TlaEx = oracle.chosenValueIsEqualToIndexedValue(scope, index)
        cmp match {
          case OperEx(TlaOper.eq, NameEx(name), ValEx(TlaInt(i))) => name == oracle.intCell.toString && i == index
          case _                                                  => false
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

  test("caseAssertions requires assertion sequences of equal length") {
    val assertionsGen: Gen[(Seq[BuilderT], Option[Seq[BuilderT]])] = for {
      i <- Gen.choose(0, assertionsA.size)
      j <- Gen.choose(0, assertionsB.size)
      opt <- Gen.option(Gen.const(assertionsB.take(j)))
    } yield (assertionsA.take(i), opt)

    val prop =
      forAll(Gen.zip(nonNegIntGen, assertionsGen)) { case (size, (assertionsIfTrue, assertionsIfFalseOpt)) =>
        val (scope, oracle) = IntOracle.create(initScope, size)
        if (assertionsIfTrue.size != oracle.size || assertionsIfFalseOpt.exists { _.size != oracle.size })
          Prop.throws(classOf[IllegalArgumentException]) {
            oracle.caseAssertions(scope, assertionsIfTrue, assertionsIfFalseOpt)
          }
        else true
      }

    check(prop, minSuccessful(1000), sizeRange(4))

  }

  test("caseAssertions constructs a collection of ITEs, or shorthands") {
    val gen: Gen[(Int, Seq[BuilderT], Option[Seq[BuilderT]])] = for {
      size <- nonNegIntGen
      opt <- Gen.option(Gen.const(assertionsB.take(size)))
    } yield (size, assertionsA.take(size), opt)

    val prop =
      forAll(gen) { case (size, assertionsIfTrue, assertionsIfFalseOpt) =>
        val (scope, oracle) = IntOracle.create(initScope, size)
        val caseEx: TlaEx = oracle.caseAssertions(scope, assertionsIfTrue, assertionsIfFalseOpt)
        size match {
          case 0 =>
            caseEx == PureArena.cellTrue(scope.arena).toBuilder.build
          case 1 =>
            caseEx == assertionsA.head.build
          case _ =>
            assertionsIfFalseOpt match {
              case None =>
                val ites = assertionsIfTrue.zipWithIndex.map { case (a, i) =>
                  tla.ite(tla.eql(oracle.intCell.toBuilder, tla.int(i)), a, tla.bool(true))
                }
                caseEx == tla.and(ites: _*).build
              case Some(assertionsIfFalse) =>
                val ites = assertionsIfTrue.zip(assertionsIfFalse).zipWithIndex.map { case ((at, af), i) =>
                  tla.ite(tla.eql(oracle.intCell.toBuilder, tla.int(i)), at, af)
                }
                caseEx == tla.and(ites: _*).build
            }
        }
      }

    check(prop, minSuccessful(1000), sizeRange(4))

  }

  // We cannot test getIndexOfChosenValueFromModel without running the solver
  test("getIndexOfChosenValueFromModel recovers the index correctly") {
    val prop =
      forAll(Gen.zip(maxSizeAndIndexGen)) { case (size, index) =>
        val ctx = new Z3SolverContext(SolverConfig.default)
        val paa = PureArenaAdapter.create(ctx) // We use PAA, since it performs the basic context initialization
        val (scope, oracle) = IntOracle.create(initScope.copy(arena = paa.arena), size)
        ctx.declareCell(oracle.intCell)

        val eql = oracle.chosenValueIsEqualToIndexedValue(scope, index)
        ctx.assertGroundExpr(eql)
        ctx.sat()
        oracle.getIndexOfChosenValueFromModel(ctx) == index
      }

    // 1000 is too many, since each run invokes the solver
    check(prop, minSuccessful(200), sizeRange(4))
  }
}

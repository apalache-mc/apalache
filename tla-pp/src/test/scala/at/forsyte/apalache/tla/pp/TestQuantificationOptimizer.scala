package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{Typed, _}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import org.junit.runner.RunWith
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper}
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import org.scalacheck.Gen
import org.scalacheck.Prop.{forAll, AnyOperators}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestQuantificationOptimizer extends AnyFunSuite with Checkers {

  val optimizer = new IntegerQuantificationOptimizer(new IdleTracker)

  val gens: IrGenerators = new IrGenerators {
    override val maxArgs: Int = 3
  }

  val ops =
    gens.simpleOperators ++ gens.logicOperators ++ gens.arithOperators ++ gens.setOperators ++ gens.functionOperators

  val rangeGen: Gen[TlaEx] = for {
    a <- gens.genTlaEx(ops)(gens.emptyContext)
    b <- gens.genTlaEx(ops)(gens.emptyContext)
  } yield tla.dotdot(a.as(IntT1()), b.as(IntT1())).as(SetT1(IntT1()))

  val boolTag = Typed(BoolT1())
  val varname = tla.name("x").as(IntT1())

  def forSetWithPredicates(
      setGen: Gen[TlaEx],
      postPredE: (TlaEx, TlaEx) => TlaEx,
      postPredA: (TlaEx, TlaEx) => TlaEx): Unit = {
    val pairGen = for {
      setEx <- setGen
      exRaw <- gens.genTlaEx(ops)(gens.emptyContext)
    } yield (setEx, exRaw)
    val prop = forAll(pairGen) { case (setEx, exRaw) =>
      // gens produces garbage w.r.t. type tags, we just force the toplevel ex to be boolean.
      val ex = exRaw.withTag(boolTag)
      val existsEx = tla.exists(varname, setEx, ex).as(BoolT1())
      val forallEx = tla.forall(varname, setEx, ex).as(BoolT1())

      val existsCond = postPredE(setEx, ex)
      val forallCond = postPredA(setEx, ex)

      val existsExpected: TlaEx = OperEx(TlaBoolOper.existsUnbounded, varname, existsCond)(boolTag)
      val forallExpected: TlaEx = OperEx(TlaBoolOper.forallUnbounded, varname, forallCond)(boolTag)

      val existsActual = optimizer(existsEx)
      val forallActual = optimizer(forallEx)

      existsActual =? existsExpected
      forallActual =? forallExpected
    }
    check(prop, minSuccessful(500), sizeRange(7))
  }

  def inBounds(lowerBound: TlaEx, upperBound: TlaEx): TlaEx = {
    val lConstraint = tla.le(lowerBound, varname).as(BoolT1())
    val uConstraint = tla.le(varname, upperBound).as(BoolT1())
    tla.and(lConstraint, uConstraint).as(BoolT1())
  }

  val ge0 = tla.ge(varname, tla.int(0).as(IntT1())).as(BoolT1())

  def postPredE(setEx: TlaEx, ex: TlaEx): TlaEx = setEx match {
    case ValEx(TlaIntSet) => ex
    case ValEx(TlaNatSet) => tla.and(ge0, ex).as(BoolT1())
    case OperEx(TlaArithOper.dotdot, lowerBound, upperBound) =>
      tla.and(inBounds(lowerBound, upperBound), ex).as(BoolT1())
    case _ => ex
  }

  def postPredA(setEx: TlaEx, ex: TlaEx): TlaEx = setEx match {
    case ValEx(TlaIntSet) => ex
    case ValEx(TlaNatSet) => tla.impl(ge0, ex).as(BoolT1())
    case OperEx(TlaArithOper.dotdot, lowerBound, upperBound) =>
      tla.impl(inBounds(lowerBound, upperBound), ex).as(BoolT1())
    case _ => ex
  }

  test("Translation of Nat") {
    val natSet = tla.natSet().as(SetT1(IntT1()))

    forSetWithPredicates(Gen.const(natSet), postPredE, postPredA)
  }

  test("Translation of Int") {
    val intSet = tla.intSet().as(SetT1(IntT1()))

    forSetWithPredicates(Gen.const(intSet), postPredE, postPredA)
  }

  test("Translation of a..b") {
    forSetWithPredicates(rangeGen, postPredE, postPredA)
  }
}

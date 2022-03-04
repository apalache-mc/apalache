package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{Typed, _}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import org.junit.runner.RunWith
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaOper}
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

  def varnameInBounds(lowerBound: TlaEx, upperBound: TlaEx): TlaEx = {
    val lConstraint = tla.le(lowerBound, varname).as(BoolT1())
    val uConstraint = tla.le(varname, upperBound).as(BoolT1())
    tla.and(lConstraint, uConstraint).as(BoolT1())
  }

  val varnameGe0 = tla.ge(varname, tla.int(0).as(IntT1())).as(BoolT1())

  def newQuantifierPredicate(oper: TlaOper, setEx: TlaEx, ex: TlaEx): TlaEx = {
    // T /\ P for \E, T => P for \A
    val outerOperatorCtor: (TlaEx, TlaEx) => BuilderEx =
      if (oper == TlaBoolOper.exists) tla.and(_, _) else tla.impl(_, _)

    setEx match {
      case ValEx(TlaIntSet) => ex
      case ValEx(TlaNatSet) => outerOperatorCtor(varnameGe0, ex).as(BoolT1())
      case OperEx(TlaArithOper.dotdot, lowerBound, upperBound) =>
        outerOperatorCtor(varnameInBounds(lowerBound, upperBound), ex).as(BoolT1())
      case _ => ex
    }
  }

  // Checks that the actual translation matches expectations, based on the shape of the set
  def withSetGen(predefSetOrRangeGen: Gen[TlaEx]): Unit = {
    val pairGen = for {
      predefSetOrRangeEx <- predefSetOrRangeGen
      exRandomTag <- gens.genTlaEx(ops)(gens.emptyContext)
    } yield (predefSetOrRangeEx, exRandomTag)
    val prop = forAll(pairGen) { case (setEx, exWithRandomTag) =>
      // gens produces garbage w.r.t. type tags, we just force the toplevel ex to be boolean.
      val ex = exWithRandomTag.withTag(boolTag)
      val existsEx = tla.exists(varname, setEx, ex).as(BoolT1())
      val forallEx = tla.forall(varname, setEx, ex).as(BoolT1())

      val expected = {
        val expectedPredicateExists = newQuantifierPredicate(TlaBoolOper.exists, setEx, ex)
        val expectedPredicateForall = newQuantifierPredicate(TlaBoolOper.forall, setEx, ex)

        val existsExpected: TlaEx = OperEx(TlaBoolOper.existsUnbounded, varname, expectedPredicateExists)(boolTag)
        val forallExpected: TlaEx = OperEx(TlaBoolOper.forallUnbounded, varname, expectedPredicateForall)(boolTag)
        (existsExpected, forallExpected)
      }

      val actual = (optimizer(existsEx), optimizer(forallEx))

      expected =? actual
    }
    check(prop, minSuccessful(500), sizeRange(7))
  }

  test("Translation of Nat") {
    val natSet = tla.natSet().as(SetT1(IntT1()))

    withSetGen(Gen.const(natSet))
  }

  test("Translation of Int") {
    val intSet = tla.intSet().as(SetT1(IntT1()))

    withSetGen(Gen.const(intSet))
  }

  test("Translation of a..b") {
    withSetGen(rangeGen)
  }
}

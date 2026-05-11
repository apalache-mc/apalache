package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTSolver
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.Checkers

class TestCrossSolverContext extends AnyFunSuite with Checkers {
  private val cvc5Config = SolverConfig.default.copy(smtSolver = SMTSolver.CVC5, z3StatsSec = 0)
  private val z3Config = SolverConfig.default.copy(smtSolver = SMTSolver.Z3, z3StatsSec = 0)

  sealed private trait IntTerm {
    def build(x: BuilderT): BuilderT
  }

  private case object Var extends IntTerm {
    override def build(x: BuilderT): BuilderT = x
  }

  private case class Const(value: Int) extends IntTerm {
    override def build(x: BuilderT): BuilderT = tla.int(value)
  }

  private case class AddConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(x: BuilderT): BuilderT = tla.plus(base.build(x), tla.int(value))
  }

  private case class SubConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(x: BuilderT): BuilderT = tla.minus(base.build(x), tla.int(value))
  }

  sealed private trait Formula {
    def build(x: BuilderT): BuilderT
  }

  private case class Eq(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.eql(lhs.build(x), rhs.build(x))
  }

  private case class Ne(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.neql(lhs.build(x), rhs.build(x))
  }

  private case class Lt(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.lt(lhs.build(x), rhs.build(x))
  }

  private case class Le(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.le(lhs.build(x), rhs.build(x))
  }

  private case class Gt(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.gt(lhs.build(x), rhs.build(x))
  }

  private case class Ge(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.ge(lhs.build(x), rhs.build(x))
  }

  private case class Not(pred: Formula) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.not(pred.build(x))
  }

  private case class And(preds: List[Formula]) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.and(preds.map(_.build(x)): _*)
  }

  private case class Or(preds: List[Formula]) extends Formula {
    override def build(x: BuilderT): BuilderT = tla.or(preds.map(_.build(x)): _*)
  }

  private val smallIntGen: Gen[Int] = Gen.choose(-5, 5)
  private val intTermGen: Gen[IntTerm] = for {
    value <- smallIntGen
    term <- Gen.oneOf[IntTerm](Var, Const(value), AddConst(Var, value), SubConst(Var, value))
  } yield term

  private val comparisonGen: Gen[Formula] = for {
    lhs <- intTermGen
    rhs <- intTermGen
    pred <- Gen.oneOf[Formula](Eq(lhs, rhs), Ne(lhs, rhs), Lt(lhs, rhs), Le(lhs, rhs), Gt(lhs, rhs), Ge(lhs, rhs))
  } yield pred

  private val formulaGen: Gen[Formula] = for {
    first <- comparisonGen
    rest <- Gen.listOfN(2, comparisonGen)
    formula <- Gen.oneOf[Formula](first, Not(first), And(first :: rest), Or(first :: rest))
  } yield formula

  private def satWith(config: SolverConfig, mkSolver: SolverConfig => SolverContext, formula: Formula): Boolean = {
    val solver = mkSolver(config)
    try {
      val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
      solver.assertGroundExpr(formula.build(arena.topCell.toBuilder))
      solver.sat()
    } finally {
      solver.dispose()
    }
  }

  test("CVC5 and Z3 agree on generated integer constraints") {
    val prop = forAll(formulaGen) { formula =>
      val cvc5Sat = satWith(cvc5Config, new Cvc5SolverContext(_), formula)
      val z3Sat = satWith(z3Config, new Z3SolverContext(_), formula)
      cvc5Sat == z3Sat
    }

    check(prop, minSuccessful(100), minSize(0), sizeRange(4))
  }
}

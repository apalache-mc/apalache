package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTSolver
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, FixedElemPtr, InvalidTlaExException}
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, SetT1, TlaType1}
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.Checkers

// This suite checks that Z3 and CVC5 agree on formulas once arena cells and membership constraints have already been
// encoded for SolverContext. It does not cover rewriter obligations such as translating TLA+ set union, intersection,
// or difference into solver-context constraints; those need rewriter or end-to-end checker coverage.
class TestCrossSolverContext extends AnyFunSuite with Checkers {
  private val cvc5Config = SolverConfig.default.copy(smtSolver = SMTSolver.CVC5, z3StatsSec = 0)
  private val z3Config = SolverConfig.default.copy(smtSolver = SMTSolver.Z3, z3StatsSec = 0)

  private case class TestCells(
      intCells: IndexedSeq[ArenaCell],
      intSet: ArenaCell,
      boolCells: IndexedSeq[ArenaCell],
      boolSet: ArenaCell)

  sealed private trait IntTerm {
    def build(cells: TestCells): BuilderT
  }

  private case class IntVar(index: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      cells.intCells(index).toBuilder
  }

  private case class Const(value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT = tla.int(value)
  }

  private case class AddConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.plus(base.build(cells), tla.int(value))
  }

  private case class SubConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.minus(base.build(cells), tla.int(value))
  }

  private case class MultConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.mult(base.build(cells), tla.int(value))
  }

  private case class DivConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.div(base.build(cells), tla.int(value))
  }

  private case class ModConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.mod(base.build(cells), tla.int(value))
  }

  private case class ExpConst(base: IntTerm, value: Int) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.exp(base.build(cells), tla.int(value))
  }

  private case class UMinus(base: IntTerm) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.uminus(base.build(cells))
  }

  private case class IteInt(boolIndex: Int, thenTerm: IntTerm, elseTerm: IntTerm) extends IntTerm {
    override def build(cells: TestCells): BuilderT =
      tla.ite(cells.boolCells(boolIndex).toBuilder, thenTerm.build(cells), elseTerm.build(cells))
  }

  sealed private trait Formula {
    def build(cells: TestCells): BuilderT
  }

  private case class Eq(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.eql(lhs.build(cells), rhs.build(cells))
  }

  private case class Ne(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.neql(lhs.build(cells), rhs.build(cells))
  }

  private case class Lt(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.lt(lhs.build(cells), rhs.build(cells))
  }

  private case class Le(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.le(lhs.build(cells), rhs.build(cells))
  }

  private case class Gt(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.gt(lhs.build(cells), rhs.build(cells))
  }

  private case class Ge(lhs: IntTerm, rhs: IntTerm) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.ge(lhs.build(cells), rhs.build(cells))
  }

  private case class IntInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.in(cells.intCells(index).toBuilder, cells.intSet.toBuilder)
  }

  private case class IntNotInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.notin(cells.intCells(index).toBuilder, cells.intSet.toBuilder)
  }

  private case class BoolVar(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      cells.boolCells(index).toBuilder
  }

  private case class BoolConst(value: Boolean) extends Formula {
    override def build(cells: TestCells): BuilderT = tla.bool(value)
  }

  private case class BoolEq(index: Int, value: Boolean) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.eql(cells.boolCells(index).toBuilder, tla.bool(value))
  }

  private case class BoolNe(index: Int, value: Boolean) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.neql(cells.boolCells(index).toBuilder, tla.bool(value))
  }

  private case class BoolInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.in(cells.boolCells(index).toBuilder, cells.boolSet.toBuilder)
  }

  private case class BoolNotInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.notin(cells.boolCells(index).toBuilder, cells.boolSet.toBuilder)
  }

  private case class Not(pred: Formula) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.not(pred.build(cells))
  }

  private case class And(preds: List[Formula]) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.and(preds.map(_.build(cells)): _*)
  }

  private case class Or(preds: List[Formula]) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.or(preds.map(_.build(cells)): _*)
  }

  private case class Implies(lhs: Formula, rhs: Formula) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.impl(lhs.build(cells), rhs.build(cells))
  }

  private case class Equiv(lhs: Formula, rhs: Formula) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.equiv(lhs.build(cells), rhs.build(cells))
  }

  private case class IteBool(condIndex: Int, thenFormula: Formula, elseFormula: Formula) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.ite(cells.boolCells(condIndex).toBuilder, thenFormula.build(cells),
          elseFormula.build(cells))
  }

  private case class Distinct(args: List[IntTerm]) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.distinct(args.map(_.build(cells)): _*)
  }

  private val smallIntGen: Gen[Int] = Gen.choose(-5, 5)
  private val nonZeroSmallIntGen: Gen[Int] = Gen.oneOf((-5 to -1) ++ (1 to 5))
  private val smallNonNegativeIntGen: Gen[Int] = Gen.choose(0, 3)
  private val intVarGen: Gen[IntVar] = Gen.choose(0, 2).map(IntVar)
  private val baseIntTermGen: Gen[IntTerm] = for {
    value <- smallIntGen
    variable <- intVarGen
    term <- Gen.oneOf[IntTerm](variable, Const(value))
  } yield term

  private val intTermGen: Gen[IntTerm] = for {
    value <- smallIntGen
    divisor <- nonZeroSmallIntGen
    exponent <- smallNonNegativeIntGen
    boolIndex <- Gen.choose(0, 1)
    variable <- intVarGen
    lhs <- baseIntTermGen
    rhs <- baseIntTermGen
    term <- Gen.oneOf[IntTerm](
        variable,
        Const(value),
        AddConst(variable, value),
        SubConst(variable, value),
        MultConst(variable, value),
        DivConst(variable, divisor),
        ModConst(variable, divisor),
        ExpConst(Const(divisor), exponent),
        UMinus(variable),
        IteInt(boolIndex, lhs, rhs),
    )
  } yield term

  private val comparisonGen: Gen[Formula] = for {
    lhs <- intTermGen
    rhs <- intTermGen
    index <- Gen.choose(0, 2)
    pred <- Gen.oneOf[Formula](Eq(lhs, rhs), Ne(lhs, rhs), Lt(lhs, rhs), Le(lhs, rhs), Gt(lhs, rhs), Ge(lhs, rhs),
        IntInSet(index), IntNotInSet(index))
  } yield pred

  private val boolAtomGen: Gen[Formula] = for {
    index <- Gen.choose(0, 1)
    value <- Gen.oneOf(true, false)
    pred <- Gen.oneOf[Formula](BoolVar(index), BoolConst(value), BoolEq(index, value), BoolNe(index, value),
        BoolInSet(index), BoolNotInSet(index))
  } yield pred

  private val distinctGen: Gen[Formula] =
    Gen.listOfN(3, intTermGen).map(Distinct)

  private val atomGen: Gen[Formula] =
    Gen.oneOf(comparisonGen, boolAtomGen, distinctGen)

  private val formulaGen: Gen[Formula] = for {
    first <- atomGen
    second <- atomGen
    third <- atomGen
    condIndex <- Gen.choose(0, 1)
    formula <- Gen.oneOf[Formula](
        first,
        Not(first),
        And(List(first, second, third)),
        Or(List(first, second, third)),
        Implies(first, second),
        Equiv(first, second),
        IteBool(condIndex, first, second),
    )
  } yield formula

  private def appendCells(
      arena: PureArenaAdapter,
      types: Seq[TlaType1]): (PureArenaAdapter, IndexedSeq[ArenaCell]) = {
    types.foldLeft((arena, Vector.empty[ArenaCell])) { case ((nextArena, cells), cellType) =>
      val arenaWithCell = nextArena.appendCell(cellType)
      (arenaWithCell, cells :+ arenaWithCell.topCell)
    }
  }

  // Build the same small arena for each solver and ask whether the generated formula is satisfiable.
  private def satWith(config: SolverConfig, mkSolver: SolverConfig => SolverContext, formula: Formula): Boolean = {
    val solver = mkSolver(config)
    try {
      val arena = PureArenaAdapter.create(solver)
      val (arenaWithInts, intCells) = appendCells(arena, Seq.fill(3)(IntT1))
      val arenaWithIntSet = arenaWithInts.appendCell(SetT1(IntT1))
      val intSet = arenaWithIntSet.topCell
      val arenaWithIntEdges = arenaWithIntSet.appendHas(intSet, intCells.map(FixedElemPtr): _*)
      val (arenaWithBools, boolCells) = appendCells(arenaWithIntEdges, Seq.fill(2)(BoolT1))
      val arenaWithBoolSet = arenaWithBools.appendCell(SetT1(BoolT1))
      val boolSet = arenaWithBoolSet.topCell
      arenaWithBoolSet.appendHas(boolSet, boolCells.map(FixedElemPtr): _*)
      val cells = TestCells(intCells, intSet, boolCells, boolSet)
      solver.assertGroundExpr(formula.build(cells))
      solver.sat()
    } finally {
      solver.dispose()
    }
  }

  test("CVC5 and Z3 agree on generated constraints over several arena cells") {
    val prop = forAll(formulaGen) { formula =>
      val cvc5Sat = satWith(cvc5Config, new Cvc5SolverContext(_), formula)
      val z3Sat = satWith(z3Config, new Z3SolverContext(_), formula)
      cvc5Sat == z3Sat
    }

    check(prop, minSuccessful(100), minSize(0), sizeRange(4))
  }

  test("CVC5 and Z3 agree on contradictory membership over arena has edges") {
    def contradictoryFormulaIsUnsatWith(config: SolverConfig, mkSolver: SolverConfig => SolverContext): Boolean = {
      val solver = mkSolver(config)
      try {
        // This exercises set-shaped arena cells and the membership constants introduced for arena `has` edges.
        // The asserted formula requires the same element to be both in and not in the same set, so both solvers
        // should report UNSAT.
        val arena = PureArenaAdapter.create(solver).appendCell(SetT1(IntT1))
        val set = arena.topCell
        val (arenaWithElems, elems) = appendCells(arena, Seq.fill(2)(IntT1))
        arenaWithElems.appendHas(set, elems.map(FixedElemPtr): _*)
        solver.assertGroundExpr(tla.and(
                tla.in(elems.head.toBuilder, set.toBuilder),
                tla.not(tla.in(elems.head.toBuilder, set.toBuilder)),
            ))
        !solver.sat()
      } finally {
        solver.dispose()
      }
    }

    val cvc5Unsat = contradictoryFormulaIsUnsatWith(cvc5Config, new Cvc5SolverContext(_))
    val z3Unsat = contradictoryFormulaIsUnsatWith(z3Config, new Z3SolverContext(_))

    assert(cvc5Unsat && z3Unsat)
  }

  test("CVC5 and Z3 reject literal membership forms") {
    def rejectsLiteralMembershipWith(config: SolverConfig, mkSolver: SolverConfig => SolverContext): Boolean = {
      val solver = mkSolver(config)
      try {
        val arena = PureArenaAdapter.create(solver).appendCell(SetT1(IntT1))
        val intSet = arena.topCell
        intercept[InvalidTlaExException] {
          solver.assertGroundExpr(tla.in(tla.int(1), intSet.toBuilder))
        }

        val boolSetArena = arena.appendCell(SetT1(BoolT1))
        val boolSet = boolSetArena.topCell
        intercept[InvalidTlaExException] {
          solver.assertGroundExpr(tla.in(tla.bool(true), boolSet.toBuilder))
        }

        true
      } finally {
        solver.dispose()
      }
    }

    val cvc5Rejects = rejectsLiteralMembershipWith(cvc5Config, new Cvc5SolverContext(_))
    val z3Rejects = rejectsLiteralMembershipWith(z3Config, new Z3SolverContext(_))

    assert(cvc5Rejects && z3Rejects)
  }

  test("CVC5 and Z3 agree on notin over bool and function set cells") {
    def contradictoryNotinFormulaIsUnsatWith(config: SolverConfig, mkSolver: SolverConfig => SolverContext): Boolean = {
      val solver = mkSolver(config)
      try {
        val arena = PureArenaAdapter.create(solver).appendCell(SetT1(BoolT1))
        val boolSet = arena.topCell
        val (arenaWithBools, boolElems) = appendCells(arena, Seq.fill(2)(BoolT1))
        arenaWithBools.appendHas(boolSet, boolElems.map(FixedElemPtr): _*)

        val funType = FunT1(IntT1, BoolT1)
        val arenaWithFunSet = arenaWithBools.appendCell(SetT1(funType))
        val funSet = arenaWithFunSet.topCell
        val (arenaWithFuns, funElems) = appendCells(arenaWithFunSet, Seq.fill(2)(funType))
        arenaWithFuns.appendHas(funSet, funElems.map(FixedElemPtr): _*)

        solver.assertGroundExpr(tla.and(
                tla.in(boolElems.head.toBuilder, boolSet.toBuilder),
                tla.notin(boolElems.head.toBuilder, boolSet.toBuilder),
                tla.in(funElems.head.toBuilder, funSet.toBuilder),
                tla.notin(funElems.head.toBuilder, funSet.toBuilder),
            ))
        !solver.sat()
      } finally {
        solver.dispose()
      }
    }

    val cvc5Unsat = contradictoryNotinFormulaIsUnsatWith(cvc5Config, new Cvc5SolverContext(_))
    val z3Unsat = contradictoryNotinFormulaIsUnsatWith(z3Config, new Z3SolverContext(_))

    assert(cvc5Unsat && z3Unsat)
  }
}

package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTSolver
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, FixedElemPtr, InvalidTlaExException}
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, SetT1, TlaEx, TlaType1}
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.Checkers

// This suite is intentionally scoped to SolverContext parity on OOPSLA19: given
// the same arena cells and direct SMT-facing constraints, Z3 and CVC5 should
// agree on satisfiability and on evaluating ground expressions after SAT.
//
// The generated properties and focused tests exercise the shared
// {Z3SolverContext,Cvc5SolverContext}.toExpr paths for names, Boolean and
// integer literals, arithmetic, equality and disequality, distinct, Boolean
// connectives, ITE, named-cell membership, notin, literal-membership rejection,
// and the OOPSLA19 membership meaning of selectInSet/storeInSet/storeNotInSet.
// For selectInSet/storeInSet/storeNotInSet, the test generator builds several
// combinations of these internal operators over the same set and element cells.
// The generated arena includes integer, Boolean, and function set cells, and each
// generated set constrains a generated subset of its cells as members. This lets
// membership/notin cases cover nontrivial set sorts without making every generated
// membership query trivially true.
//
// Things NOT covered:
//
// We don't exercise selectInFun, storeNotInFun, or the ternary/function-update
// form of storeInSet directly. Meaningful tests for those operators need either
// a complete OOPSLA19 function value produced by the rewriter or an
// Arrays/FunArrays function cell. This suite only builds bare arena cells plus
// simple membership constraints. Nested selectInSet(selectInFun(...), ...),
// smtMap, and unconstrainArray are also left out here because they are
// array-specific or Z3-only paths.
//
// Rewriter paths, including set algebra such as union, intersection, and
// difference, are covered by TestRewriterWithOOPSLA19 and
// TestRewriterWithCvc5OOPSLA19.
//
// The rewriter tests also exercise the success path of SolverContext.checkConsistency
// indirectly, because SymbStateRewriterImpl.rewriteUntilDone calls it whenever
// rewriting converges to a cell.
class TestCrossSolverContextWithOOPSLA19 extends AnyFunSuite with Checkers {
  private val cvc5Config = SolverConfig.default.copy(smtSolver = SMTSolver.CVC5, z3StatsSec = 0)
  private val z3Config = SolverConfig.default.copy(smtSolver = SMTSolver.Z3, z3StatsSec = 0)

  // Describes the generated arena:
  // - The counts say how many cells of each sort to create.
  // - The member-index sets say which of those cells should be constrained as members of the
  //   corresponding set; all remaining cells are constrained as non-members.
  private case class TestShape(
      intCount: Int,
      intMemberIndices: Set[Int],
      boolCount: Int,
      boolMemberIndices: Set[Int],
      funCount: Int,
      funMemberIndices: Set[Int])

  private case class TestCells(
      intCells: IndexedSeq[ArenaCell],
      intSet: ArenaCell,
      boolCells: IndexedSeq[ArenaCell],
      boolSet: ArenaCell,
      funCells: IndexedSeq[ArenaCell],
      funSet: ArenaCell)

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

  private case class BoolCellEq(lhsIndex: Int, rhsIndex: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.eql(cells.boolCells(lhsIndex).toBuilder, cells.boolCells(rhsIndex).toBuilder)
  }

  private case class BoolCellNe(lhsIndex: Int, rhsIndex: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.neql(cells.boolCells(lhsIndex).toBuilder, cells.boolCells(rhsIndex).toBuilder)
  }

  private case class BoolInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.in(cells.boolCells(index).toBuilder, cells.boolSet.toBuilder)
  }

  private case class BoolNotInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.notin(cells.boolCells(index).toBuilder, cells.boolSet.toBuilder)
  }

  private case class FunInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.in(cells.funCells(index).toBuilder, cells.funSet.toBuilder)
  }

  private case class FunNotInSet(index: Int) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.notin(cells.funCells(index).toBuilder, cells.funSet.toBuilder)
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
      tla.ite(cells.boolCells(condIndex).toBuilder, thenFormula.build(cells), elseFormula.build(cells))
  }

  private case class Distinct(args: List[IntTerm]) extends Formula {
    override def build(cells: TestCells): BuilderT =
      tla.distinct(args.map(_.build(cells)): _*)
  }

  private val smallIntGen: Gen[Int] = Gen.choose(-5, 5)
  private val nonZeroSmallIntGen: Gen[Int] = Gen.oneOf((-5 to -1) ++ (1 to 5))
  private val smallNonNegativeIntGen: Gen[Int] = Gen.choose(0, 3)
  private val testShapeGen: Gen[TestShape] = for {
    intCount <- Gen.choose(1, 4)
    intMemberIndices <- Gen.someOf(0 until intCount).map(_.toSet)
    boolCount <- Gen.choose(1, 4)
    boolMemberIndices <- Gen.someOf(0 until boolCount).map(_.toSet)
    funCount <- Gen.choose(1, 3)
    funMemberIndices <- Gen.someOf(0 until funCount).map(_.toSet)
  } yield TestShape(
      intCount,
      intMemberIndices,
      boolCount,
      boolMemberIndices,
      funCount,
      funMemberIndices,
  )

  private def intVarGen(shape: TestShape): Gen[IntVar] = Gen.choose(0, shape.intCount - 1).map(IntVar)

  private def baseIntTermGen(shape: TestShape): Gen[IntTerm] = for {
    value <- smallIntGen
    variable <- intVarGen(shape)
    term <- Gen.oneOf[IntTerm](variable, Const(value))
  } yield term

  private def intTermGen(shape: TestShape): Gen[IntTerm] = for {
    value <- smallIntGen
    divisor <- nonZeroSmallIntGen
    exponent <- smallNonNegativeIntGen
    boolIndex <- Gen.choose(0, shape.boolCount - 1)
    variable <- intVarGen(shape)
    lhs <- baseIntTermGen(shape)
    rhs <- baseIntTermGen(shape)
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

  private def comparisonGen(shape: TestShape): Gen[Formula] = for {
    lhs <- intTermGen(shape)
    rhs <- intTermGen(shape)
    index <- Gen.choose(0, shape.intCount - 1)
    pred <- Gen.oneOf[Formula](
        Eq(lhs, rhs),
        Ne(lhs, rhs),
        Lt(lhs, rhs),
        Le(lhs, rhs),
        Gt(lhs, rhs),
        Ge(lhs, rhs),
        IntInSet(index),
        IntNotInSet(index),
    )
  } yield pred

  private def boolAtomGen(shape: TestShape): Gen[Formula] = for {
    index <- Gen.choose(0, shape.boolCount - 1)
    otherIndex <- Gen.choose(0, shape.boolCount - 1)
    value <- Gen.oneOf(true, false)
    pred <- Gen.oneOf[Formula](
        BoolVar(index),
        BoolConst(value),
        BoolEq(index, value),
        BoolNe(index, value),
        BoolCellEq(index, otherIndex),
        BoolCellNe(index, otherIndex),
        BoolInSet(index),
        BoolNotInSet(index),
    )
  } yield pred

  private def funMembershipGen(shape: TestShape): Gen[Formula] = for {
    index <- Gen.choose(0, shape.funCount - 1)
    pred <- Gen.oneOf[Formula](FunInSet(index), FunNotInSet(index))
  } yield pred

  private def distinctGen(shape: TestShape): Gen[Formula] =
    Gen.frequency(
        1 -> Gen.const(Distinct(Nil)),
        1 -> intTermGen(shape).map(term => Distinct(List(term))),
        8 -> Gen.listOfN(3, intTermGen(shape)).map(Distinct),
    )

  private def atomGen(shape: TestShape): Gen[Formula] =
    Gen.oneOf(comparisonGen(shape), boolAtomGen(shape), funMembershipGen(shape), distinctGen(shape))

  private def formulaGen(shape: TestShape): Gen[Formula] = for {
    first <- atomGen(shape)
    second <- atomGen(shape)
    third <- atomGen(shape)
    condIndex <- Gen.choose(0, shape.boolCount - 1)
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

  private case class FormulaCase(shape: TestShape, formula: Formula)

  private val formulaCaseGen: Gen[FormulaCase] = for {
    shape <- testShapeGen
    formula <- formulaGen(shape)
  } yield FormulaCase(shape, formula)

  private case class EvalCase(
      shape: TestShape,
      intAssignments: IndexedSeq[Int],
      boolAssignments: IndexedSeq[Boolean],
      intTerm: IntTerm,
      formula: Formula)

  private val evalCaseGen: Gen[EvalCase] = for {
    shape <- testShapeGen
    intAssignments <- Gen.listOfN(shape.intCount, smallIntGen).map(_.toIndexedSeq)
    boolAssignments <- Gen.listOfN(shape.boolCount, Gen.oneOf(true, false)).map(_.toIndexedSeq)
    intTerm <- intTermGen(shape)
    formula <- formulaGen(shape)
  } yield EvalCase(shape, intAssignments, boolAssignments, intTerm, formula)

  sealed private trait InternalMembershipCase {
    def build(set: ArenaCell, elems: IndexedSeq[ArenaCell]): BuilderT
  }

  private case class StoreInAndSelectInSet(elemIndex: Int) extends InternalMembershipCase {
    override def build(set: ArenaCell, elems: IndexedSeq[ArenaCell]): BuilderT =
      tla.and(
          tla.storeInSet(elems(elemIndex).toBuilder, set.toBuilder),
          tla.selectInSet(elems(elemIndex).toBuilder, set.toBuilder),
      )
  }

  private case class StoreNotInAndSelectInSet(elemIndex: Int) extends InternalMembershipCase {
    override def build(set: ArenaCell, elems: IndexedSeq[ArenaCell]): BuilderT =
      tla.and(
          tla.storeNotInSet(elems(elemIndex).toBuilder, set.toBuilder),
          tla.selectInSet(elems(elemIndex).toBuilder, set.toBuilder),
      )
  }

  private case class StoreInAndStoreNotInSet(inIndex: Int, notInIndex: Int) extends InternalMembershipCase {
    override def build(set: ArenaCell, elems: IndexedSeq[ArenaCell]): BuilderT =
      tla.and(
          tla.storeInSet(elems(inIndex).toBuilder, set.toBuilder),
          tla.storeNotInSet(elems(notInIndex).toBuilder, set.toBuilder),
      )
  }

  private case class InternalMembershipFormulaCase(elemCount: Int, internalMembershipCase: InternalMembershipCase)

  private def internalMembershipCaseGen(elemCount: Int): Gen[InternalMembershipCase] = for {
    elemIndex <- Gen.choose(0, elemCount - 1)
    otherElemIndex <- Gen.choose(0, elemCount - 1)
    internalMembershipCase <- Gen.oneOf[InternalMembershipCase](
        StoreInAndSelectInSet(elemIndex),
        StoreNotInAndSelectInSet(elemIndex),
        StoreInAndStoreNotInSet(elemIndex, otherElemIndex),
    )
  } yield internalMembershipCase

  private val internalMembershipFormulaCaseGen: Gen[InternalMembershipFormulaCase] = for {
    elemCount <- Gen.choose(1, 4)
    internalMembershipCase <- internalMembershipCaseGen(elemCount)
  } yield InternalMembershipFormulaCase(elemCount, internalMembershipCase)

  private def appendCells(
      arena: PureArenaAdapter,
      types: Seq[TlaType1]): (PureArenaAdapter, IndexedSeq[ArenaCell]) = {
    types.foldLeft((arena, Vector.empty[ArenaCell])) { case ((nextArena, cells), cellType) =>
      val arenaWithCell = nextArena.appendCell(cellType)
      (arenaWithCell, cells :+ arenaWithCell.topCell)
    }
  }

  // Build the arena shape selected by the generator: some integer cells with one integer set, some Boolean cells with
  // one Boolean set, and some function cells with one function set. The appendHas calls register the membership
  // constants that the solver contexts need for every candidate cell/set pair. The generated shape decides which
  // candidates are actual members: we assert storeInSet for member cells and storeNotInSet for non-member cells so
  // generated membership formulas see both positive and negative constraints.
  private def buildTestCells(solver: SolverContext, shape: TestShape): TestCells = {
    val arena = PureArenaAdapter.create(solver)
    val (arenaWithInts, intCells) = appendCells(arena, Seq.fill(shape.intCount)(IntT1))
    val arenaWithIntSet = arenaWithInts.appendCell(SetT1(IntT1))
    val intSet = arenaWithIntSet.topCell
    val arenaWithIntEdges = arenaWithIntSet.appendHas(intSet, intCells.map(FixedElemPtr): _*)
    val (arenaWithBools, boolCells) = appendCells(arenaWithIntEdges, Seq.fill(shape.boolCount)(BoolT1))
    val arenaWithBoolSet = arenaWithBools.appendCell(SetT1(BoolT1))
    val boolSet = arenaWithBoolSet.topCell
    val arenaWithBoolEdges = arenaWithBoolSet.appendHas(boolSet, boolCells.map(FixedElemPtr): _*)
    val funType = FunT1(IntT1, BoolT1)
    val (arenaWithFuns, funCells) = appendCells(arenaWithBoolEdges, Seq.fill(shape.funCount)(funType))
    val arenaWithFunSet = arenaWithFuns.appendCell(SetT1(funType))
    val funSet = arenaWithFunSet.topCell
    arenaWithFunSet.appendHas(funSet, funCells.map(FixedElemPtr): _*)
    assertMembership(solver, intCells, intSet, shape.intMemberIndices)
    assertMembership(solver, boolCells, boolSet, shape.boolMemberIndices)
    assertMembership(solver, funCells, funSet, shape.funMemberIndices)
    TestCells(intCells, intSet, boolCells, boolSet, funCells, funSet)
  }

  private def assertMembership(
      solver: SolverContext,
      cells: IndexedSeq[ArenaCell],
      set: ArenaCell,
      memberIndices: Set[Int]): Unit = {
    cells.zipWithIndex.foreach { case (cell, index) =>
      val membership =
        if (memberIndices.contains(index)) tla.storeInSet(cell.toBuilder, set.toBuilder)
        else tla.storeNotInSet(cell.toBuilder, set.toBuilder)
      solver.assertGroundExpr(membership)
    }
  }

  // Build the same small arena for each solver and ask whether the generated formula is satisfiable.
  private def satWith(
      config: SolverConfig,
      mkSolver: SolverConfig => SolverContext,
      formulaCase: FormulaCase): Boolean = {
    val solver = mkSolver(config)
    try {
      val cells = buildTestCells(solver, formulaCase.shape)
      solver.assertGroundExpr(formulaCase.formula.build(cells))
      solver.sat()
    } finally {
      solver.dispose()
    }
  }

  // Build the same small arena for each solver, then bind the generated integer and Boolean cells to concrete values.
  // For example, intAssignments.zip(cells.intCells) may produce (3, c5), (-1, c6), (5, c7), and we assert c5 = 3,
  // c6 = -1, c7 = 5. The generated integer term is then evaluated over those cells, e.g. c6 + 4 evaluates to 3.
  // The returned pair is (generated integer term value, generated Boolean formula value).
  private def evalWith(
      config: SolverConfig,
      mkSolver: SolverConfig => SolverContext,
      evalCase: EvalCase): (TlaEx, TlaEx) = {
    val solver = mkSolver(config)
    try {
      val cells = buildTestCells(solver, evalCase.shape)
      evalCase.intAssignments.zip(cells.intCells).foreach { case (value, cell) =>
        solver.assertGroundExpr(tla.eql(cell.toBuilder, tla.int(value)))
      }
      evalCase.boolAssignments.zip(cells.boolCells).foreach { case (value, cell) =>
        solver.assertGroundExpr(tla.eql(cell.toBuilder, tla.bool(value)))
      }
      assert(solver.sat())
      (solver.evalGroundExpr(evalCase.intTerm.build(cells)), solver.evalGroundExpr(evalCase.formula.build(cells)))
    } finally {
      solver.dispose()
    }
  }

  test("CVC5 and Z3 agree on generated constraints over several arena cells") {
    val prop = forAll(formulaCaseGen) { formulaCase =>
      val cvc5Sat = satWith(cvc5Config, new Cvc5SolverContext(_), formulaCase)
      val z3Sat = satWith(z3Config, new Z3SolverContext(_), formulaCase)
      cvc5Sat == z3Sat
    }

    check(prop, minSuccessful(100), minSize(0), sizeRange(4))
  }

  test("CVC5 and Z3 agree when evaluating generated ground expressions after sat") {
    val prop = forAll(evalCaseGen) { evalCase =>
      val cvc5Values = evalWith(cvc5Config, new Cvc5SolverContext(_), evalCase)
      val z3Values = evalWith(z3Config, new Z3SolverContext(_), evalCase)
      cvc5Values == z3Values
    }

    check(prop, minSuccessful(100), minSize(0), sizeRange(4))
  }

  test("CVC5 and Z3 agree on generated internal membership formulas in OOPSLA19") {
    def internalMembershipFormulaIsSatWith(
        config: SolverConfig,
        mkSolver: SolverConfig => SolverContext,
        formulaCase: InternalMembershipFormulaCase): Boolean = {
      val solver = mkSolver(config)
      try {
        val arena = PureArenaAdapter.create(solver).appendCell(SetT1(IntT1))
        val set = arena.topCell
        val (arenaWithElems, elems) = appendCells(arena, Seq.fill(formulaCase.elemCount)(IntT1))
        arenaWithElems.appendHas(set, elems.map(FixedElemPtr): _*)

        solver.assertGroundExpr(formulaCase.internalMembershipCase.build(set, elems))
        solver.sat()
      } finally {
        solver.dispose()
      }
    }

    val prop = forAll(internalMembershipFormulaCaseGen) { formulaCase =>
      val cvc5Sat = internalMembershipFormulaIsSatWith(cvc5Config, new Cvc5SolverContext(_), formulaCase)
      val z3Sat = internalMembershipFormulaIsSatWith(z3Config, new Z3SolverContext(_), formulaCase)
      cvc5Sat == z3Sat
    }

    check(prop, minSuccessful(100), minSize(0), sizeRange(4))
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

}

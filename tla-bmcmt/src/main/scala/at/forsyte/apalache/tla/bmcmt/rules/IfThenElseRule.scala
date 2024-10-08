package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.TlaControlOper
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, IntT1, OperEx}
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}

/**
 * Rewriting rule for IF A THEN B ELSE C.
 *
 * @author
 *   Igor Konnov
 */
class IfThenElseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickFrom = new CherryPick(rewriter)
  private val simplifier = new ConstSimplifierForSmt()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaControlOper.ifThenElse, _, _, _) => true
      case _                                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        var nextState = rewriter.rewriteUntilDone(state.setRex(predEx))
        val predCell = nextState.asCell
        // Some rules immediately return TRUE or FALSE. In combination with assignments, this may lead to rewriting errors.
        // See: TestSymbStateRewriterBool.test("""IF-THEN-ELSE with \E...""")
        // In such cases, we should prune the branches
        if (simplifier.isTrueConst(predCell.toBuilder)) {
          rewriter.rewriteUntilDone(nextState.setRex(thenEx))
        } else if (simplifier.isFalseConst(predCell.toBuilder)) {
          rewriter.rewriteUntilDone(nextState.setRex(elseEx))
        } else {
          nextState = rewriter.rewriteUntilDone(nextState.setRex(thenEx))
          val thenCell = nextState.asCell
          nextState = rewriter.rewriteUntilDone(nextState.setRex(elseEx))
          val elseCell = nextState.asCell

          val resultType = CellT.fromTypeTag(ex.typeTag)
          resultType match {
            // basic types, we can use SMT equality
            case CellTFrom(BoolT1) | CellTFrom(IntT1) | CellTFrom(ConstT1(_)) =>
              iteBasic(nextState, resultType, predCell.toBuilder, thenCell, elseCell)

            // sets, functions, records, tuples, sequence: use pick
            case _ => iteGeneral(nextState, predCell.toBuilder, thenCell, elseCell)
          }
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def iteBasic(
      state: SymbState,
      commonType: CellT,
      pred: BuilderT,
      thenCell: ArenaCell,
      elseCell: ArenaCell) = {
    val newArena = state.arena.appendCellOld(commonType)
    val newCell = newArena.topCell
    // it's OK to use the SMT equality and ite, as we are dealing with the basic types here
    val iffIte = tla.eql(newCell.toBuilder, tla.ite(pred, thenCell.toBuilder, elseCell.toBuilder))
    rewriter.solverContext.assertGroundExpr(iffIte)
    state.setArena(newArena).setRex(newCell.toBuilder)
  }

  // Just use PICK FROM { thenValue, elseValue } to pick one of the two values.
  // The cool thing is that we do not have to compare the results anymore. It is all defined by the oracle.
  private def iteGeneral(
      state: SymbState,
      pred: BuilderT,
      thenCell: ArenaCell,
      elseCell: ArenaCell) = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _

    // introduce an oracle \in 0..1. We use integers as the pick rules do so.
    val (nextState, oracle) = pickFrom.oracleFactory.newDefaultOracle(state, 2)
    // require the oracle value to match the predicate: oracle = 1 iff pred = true
    solverAssert(tla.equiv(pred, oracle.whenEqualTo(nextState, 1)))
    // Pick a cell. Mind the order, oracle = 1 is the then branch, whereas oracle = 0 is the else branch.
    pickFrom.pickByOracle(nextState, oracle, Seq(elseCell, thenCell), nextState.arena.cellFalse().toBuilder)
  }
}

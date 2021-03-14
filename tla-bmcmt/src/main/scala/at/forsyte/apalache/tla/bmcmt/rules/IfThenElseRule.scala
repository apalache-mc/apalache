package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaControlOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * Rewriting rule for IF A THEN B ELSE C.
 *
 * @author Igor Konnov
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
      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        var nextState = rewriter.rewriteUntilDone(state.setRex(predEx))
        val predCell = nextState.asCell
        // Some rules immediately return TRUE or FALSE. In combination with assignments, this may lead to rewriting errors.
        // See: TestSymbStateRewriterBool.test("""IF-THEN-ELSE with \E...""")
        // In such cases, we should prune the branches
        if (simplifier.isTrueConst(predCell.toNameEx)) {
          rewriter.rewriteUntilDone(nextState.setRex(thenEx))
        } else if (simplifier.isFalseConst(predCell.toNameEx)) {
          rewriter.rewriteUntilDone(nextState.setRex(elseEx))
        } else {
          nextState = rewriter.rewriteUntilDone(nextState.setRex(thenEx))
          val thenCell = nextState.asCell
          nextState = rewriter.rewriteUntilDone(nextState.setRex(elseEx))
          val elseCell = nextState.asCell

          val resultType = rewriter.typeFinder.compute(state.ex, BoolT(), thenCell.cellType, elseCell.cellType)
          resultType match {
            // basic types, we can use SMT equality
            case BoolT() | IntT() | ConstT() => iteBasic(nextState, resultType, predCell.toNameEx, thenCell, elseCell)

            // sets, functions, records, tuples, sequence: use pick
            case _ => iteGeneral(nextState, resultType, predCell.toNameEx, thenCell, elseCell)
          }
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def iteBasic(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    val newArena = state.arena.appendCell(commonType)
    val newCell = newArena.topCell
    // it's OK to use the SMT equality and ite, as we are dealing with the basic types here
    val iffIte = tla.eql(newCell.toNameEx, tla.ite(pred, thenCell.toNameEx, elseCell.toNameEx))
    rewriter.solverContext.assertGroundExpr(iffIte)
    state.setArena(newArena).setRex(newCell.toNameEx)
  }

  // Just use PICK FROM { thenValue, elseValue } to pick one of the two values.
  // The cool thing is that we do not have to compare the results anymore. It is all defined by the oracle.
  private def iteGeneral(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _

    // introduce an oracle \in 0..1. We use integers as the pick rules do so.
    val (nextState, oracle) = pickFrom.oracleFactory.newDefaultOracle(state, 2)
    // require the oracle value to match the predicate: oracle = 1 iff pred = true
    solverAssert(tla.equiv(pred, oracle.whenEqualTo(nextState, 1)))
    // Pick a cell. Mind the order, oracle = 1 is the then branch, whereas oracle = 0 is the else branch.
    pickFrom.pickByOracle(nextState, oracle, Seq(elseCell, thenCell), nextState.arena.cellFalse().toNameEx)
  }
}

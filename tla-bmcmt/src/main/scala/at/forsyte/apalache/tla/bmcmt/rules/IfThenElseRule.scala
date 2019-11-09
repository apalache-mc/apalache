package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaControlOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-ITE[1-6].
  *
  * @author Igor Konnov
  */
class IfThenElseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickFrom = new CherryPick(rewriter)
  private val simplifier = new ConstSimplifierForSmt()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaControlOper.ifThenElse, _, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        var nextState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(predEx))
        val predCell = nextState.asCell
        // Some rules immediately return TRUE or FALSE. In combination with assignments, this may lead to rewriting errors.
        // See: TestSymbStateRewriterBool.test("""IF-THEN-ELSE with \E...""")
        // In such cases, we should prune the branches
        if (simplifier.isTrueConst(predCell)) {
          rewriter.coerce(rewriter.rewriteUntilDone(nextState.setRex(thenEx)), state.theory)
        } else if (simplifier.isFalseConst(predCell)) {
          rewriter.coerce(rewriter.rewriteUntilDone(nextState.setRex(elseEx)), state.theory)
        } else {
          nextState = rewriter.rewriteUntilDone(nextState.setRex(thenEx))
          val thenCell = nextState.asCell
          nextState = rewriter.rewriteUntilDone(nextState.setRex(elseEx))
          val elseCell = nextState.asCell

          val resultType = rewriter.typeFinder.compute(state.ex, BoolT(), thenCell.cellType, elseCell.cellType)
          val finalState =
            resultType match {
              // basic types, we can use SMT equality
              case BoolT() | IntT() | ConstT() => iteBasic(nextState, resultType, predCell, thenCell, elseCell)

              // sets, functions, records, tuples, sequence: use pick
              case _ => iteGeneral(nextState, resultType, predCell, thenCell, elseCell)
            }
          rewriter.coerce(finalState, state.theory) // coerce to the source theory
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  /*
  /**
    * <p>This function adds the constraints that allow us to properly treat side effects such as Assert(..).
    * It essentially says that the failure predicates generated for each branch can be only activated,
    * if the branch condition is satisfied. Without this condition the expressions such as
    * "IF e \in DOMAIN f THEN f[e] ELSE default" would report a false runtime error.</p>
    *
    * TODO: This method generates an enormous number of constraints on large benchmarks. Find a better solution.
    *
    * @param predState the state after rewriting the condition
    * @param thenState the state after rewriting the then branch
    * @param elseState the state after rewriting the else branch
    */
  private def coverFailurePredicates(predState: SymbState, thenState: SymbState, elseState: SymbState): Unit = {
    // XXX: future self, the operations on the maps and sets are probably expensive. Optimize.
    // a response from the future self: the whole thing was a bad idea.
    val predsBefore = Set(predState.arena.findCellsByType(FailPredT()): _*)
    val thenPreds = Set(thenState.arena.findCellsByType(FailPredT()): _*) -- predsBefore
    val elsePreds = Set(elseState.arena.findCellsByType(FailPredT()): _*) -- thenPreds
    val cond = predState.ex
    // for each failure fp on the then branch, fp => cond
    thenPreds.foreach(fp => rewriter.solverContext.assertGroundExpr(tla.or(tla.not(fp), cond)))
    // for each failure fp on the else branch, fp => ~cond
    elsePreds.foreach(fp => rewriter.solverContext.assertGroundExpr(tla.or(tla.not(fp), tla.not(cond))))
  }
  */

  private def iteBasic(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    val newArena = state.arena.appendCell(commonType)
    val newCell = newArena.topCell
    // it's OK to use the SMT equality and ite, as we are dealing with the basic types here
    val iffIte = tla.eql(newCell, tla.ite(pred, thenCell, elseCell))
    rewriter.solverContext.assertGroundExpr(iffIte)
    state.setArena(newArena).setRex(newCell.toNameEx).setTheory(CellTheory())
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
    pickFrom.pickByOracle(nextState, oracle, Seq(elseCell, thenCell), nextState.arena.cellFalse())
  }
}

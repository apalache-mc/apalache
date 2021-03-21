package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, TlaEx, TlaType1, TupT1, ValEx}
import com.typesafe.scalalogging.LazyLogging

/**
 * Implements the rules for TLC operators.
 *
 * @author Igor Konnov
 */
class TlcRule(rewriter: SymbStateRewriter) extends RewritingRule with LazyLogging {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlcOper.print, _, _)        => true
      case OperEx(TlcOper.printT, _)          => true
      case OperEx(TlcOper.assert, _, _)       => true
      case OperEx(TlcOper.colonGreater, _, _) => true
      case OperEx(TlcOper.atat, _, _)         => true
      case _                                  => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlcOper.print, _, _) | OperEx(TlcOper.printT, _) =>
        state.setRex(state.arena.cellTrue().toNameEx)

      case OperEx(TlcOper.assert, value, ValEx(TlaStr(message))) =>
        // We do not support Assert as it is intrinsically imperative.
        // There is an open issue on that: https://github.com/informalsystems/apalache/issues/23
        // Maybe one day we find a way to implement it via slicing.
        logger.warn(s"""Met TLC!Assert("$message"). Interpreting it as TRUE.""")
        state.setRex(state.arena.cellTrue().toNameEx)

      case OperEx(TlcOper.colonGreater, arg, res) => // a :> b
        // Here we deviate a bit from the type checker.
        // Instead of constructing a function, which introduces a lot of constraints,
        // we just introduce a tuple. The reason is that a :> b is always used together with @@.
        val argT = TlaType1.fromTypeTag(arg.typeTag)
        val resT = TlaType1.fromTypeTag(res.typeTag)
        val tup = tla
          .tuple(arg, res)
          .typed(TupT1(argT, resT))
        state.setRex(tup)

      case OperEx(TlcOper.atat, funEx, pairEx) =>
        // f @@ a :> b, the type checker should take care of types
        extendFun(state, funEx, pairEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def extendFun(state: SymbState, funEx: TlaEx, pairEx: TlaEx): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = rewriter.rewriteUntilDone(state.setRex(funEx))
    val funCell = nextState.asCell
    val relation = nextState.arena.getCdm(funCell)
    val relationCells = nextState.arena.getHas(relation)
    nextState = rewriter.rewriteUntilDone(nextState.setRex(pairEx))
    val newPair = nextState.asCell
    nextState = nextState.updateArena(_.appendCell(funCell.cellType))
    val newFunCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendCell(relation.cellType))
    val newRelation = nextState.arena.topCell
    nextState = nextState.updateArena(_.setCdm(newFunCell, newRelation)
          .appendHas(newRelation, newPair +: relationCells: _*))
    // As we pass the expressions to SMT, we could use untyped expressions.
    // We don't do it, in order to avoid mixing untyped and typed expressions in the same class.
    val types =
      Map("b" -> BoolT1(), "p" -> TlaType1.fromTypeTag(pairEx.typeTag), "r" -> TlaType1.fromTypeTag(funEx.typeTag))
    // the new pair unconditionally belongs to the new cell
    solverAssert(tla.in(newPair.toNameEx ? "p", newRelation.toNameEx ? "r").typed(types, "b"))
    for (oldPair <- relationCells) {
      val inOld = tla.in(oldPair.toNameEx ? "p", relation.toNameEx ? "r").typed(types, "b")
      val inNew = tla.in(oldPair.toNameEx ? "p", newRelation.toNameEx ? "r").typed(types, "b")
      solverAssert(tla.equiv(inNew, inOld).typed(BoolT1()))
    }

    nextState.setRex(newFunCell.toNameEx)
  }
}

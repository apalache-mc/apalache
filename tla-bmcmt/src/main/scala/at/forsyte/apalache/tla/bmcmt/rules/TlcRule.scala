package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, OperEx, SetT1, TlaEx, TlaType1, TupT1, ValEx}
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

      case ex @ OperEx(TlcOper.colonGreater, arg, res) => // a :> b
        // We introduce a singleton function [ x \in {arg} |-> res ].
        val funT1 = TlaType1.fromTypeTag(ex.typeTag).asInstanceOf[FunT1]
        // produce a temporary name
        val tempName = "__t" + ex.ID
        val funEx = tla
          .funDef(res, tla.name(tempName).typed(funT1.arg), tla.enumSet(arg).typed(SetT1(funT1.res)))
          .typed(funT1)
        // translate the new function definition with rewriter
        rewriter.rewriteUntilDone(state.setRex(funEx))

      case OperEx(TlcOper.atat, lhs, rhs) =>
        // lhs @@ rhs, the type checker should take care of types
        extendFun(state, lhs, rhs)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def extendFun(state: SymbState, leftFunEx: TlaEx, rightFunEx: TlaEx): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _

    val funT1 = TlaType1.fromTypeTag(leftFunEx.typeTag).asInstanceOf[FunT1]
    var nextState = rewriter.rewriteUntilDone(state.setRex(leftFunEx))
    val leftFunCell = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(rightFunEx))
    val rightFunCell = nextState.asCell
    // Blindly concatenate both relations. If the domains of the functions intersect, we may produce an unsound encoding.
    // As TLC!@@ is used only to decode counterexamples, it should be ok. Otherwise, we would produce a lot of constraints.
    val leftRelation = nextState.arena.getCdm(leftFunCell)
    val leftPairs = nextState.arena.getHas(leftRelation)
    val rightRelation = nextState.arena.getCdm(rightFunCell)
    val rightPairs = nextState.arena.getHas(rightRelation)
    val jointPairs = leftPairs ++ rightPairs
    nextState = nextState.updateArena(_.appendCell(leftFunCell.cellType))
    val newFunCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendCell(leftRelation.cellType))
    val newRelation = nextState.arena.topCell
    nextState = nextState.updateArena(_.setCdm(newFunCell, newRelation)
          .appendHas(newRelation, jointPairs: _*))

    // As we pass the expressions to SMT, we could use untyped expressions.
    // We don't do it, in order to avoid mixing untyped and typed expressions in the same class.
    val pairT = TupT1(funT1.arg, funT1.res)
    val types =
      Map("b" -> BoolT1(), "p" -> pairT, "r" -> SetT1(pairT))
    // the new pair unconditionally belongs to the new cell
    for (pair <- leftPairs) {
      val inOld = tla.in(pair.toNameEx ? "p", leftRelation.toNameEx ? "r") ? "b"
      val inNew = tla.in(pair.toNameEx ? "p", newRelation.toNameEx ? "r") ? "b"
      solverAssert(tla.equiv(inNew, inOld).typed(types, "b"))
    }
    for (pair <- rightPairs) {
      val inOld = tla.in(pair.toNameEx ? "p", rightRelation.toNameEx ? "r") ? "b"
      val inNew = tla.in(pair.toNameEx ? "p", newRelation.toNameEx ? "r") ? "b"
      solverAssert(tla.equiv(inNew, inOld).typed(types, "b"))
    }

    nextState.setRex(newFunCell.toNameEx)
  }
}

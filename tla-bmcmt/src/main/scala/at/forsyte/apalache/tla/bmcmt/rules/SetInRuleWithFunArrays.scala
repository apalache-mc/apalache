package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, OperEx, TlaEx}

/**
 * Rewrites set membership tests: x \in S, x \in SUBSET S, and x \in [S -> T].
 *
 * @author
 *   Rodrigo Otoni
 */
class SetInRuleWithFunArrays(rewriter: SymbStateRewriter) extends SetInRule(rewriter) {
  new ConstSimplifierForSmt

  override protected def funSetIn(state: SymbState, funsetCell: ArenaCell, funCell: ArenaCell): SymbState = {
    // checking whether f \in [S -> T]
    def flagTypeError(): Nothing = {
      val msg = s"Not implemented (open an issue): f \\in S for f: %s and S: %s."
        .format(funCell.cellType, funsetCell.cellType)
      throw new RewriterException(msg, state.ex)
    }

    funCell.cellType match {
      case CellTFrom(FunT1(domT, _)) => domT // OK
      case _                         => flagTypeError()
    }
    funsetCell.cellType match {
      case FinFunSetT(PowSetT(_), _) | FinFunSetT(FinFunSetT(_, _), _) =>
        flagTypeError()
      case _ => () // OK
    }

    val funDom = state.arena.getDom(funCell)
    val funsetDom = state.arena.getDom(funsetCell)
    val funsetCdm = state.arena.getCdm(funsetCell)
    var nextState = state

    def onPair(arg: ArenaCell): TlaEx = {
      val funApp = OperEx(TlaFunOper.app, funCell.toNameEx, arg.toNameEx)
      nextState = rewriter.rewriteUntilDone(nextState.setRex(funApp))
      val funAppRes = nextState.asCell

      funsetCdm.cellType match {
        case _: PowSetT =>
          val powSetDom = nextState.arena.getDom(funsetCdm)
          val subsetEq = tla.subseteq(funAppRes.toNameEx, powSetDom.toNameEx)
          nextState = rewriter.rewriteUntilDone(nextState.setRex(subsetEq))
          nextState.asCell.toNameEx

        case _ =>
          val funsetCdmElems = nextState.arena.getHas(funsetCdm)

          // cache equality constraints first
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, funsetCdmElems.map((_, funAppRes)))

          def inAndEq(elem: ArenaCell) = {
            tla.and(tla.apalacheSelectInSet(elem.toNameEx, funsetCdm.toNameEx),
                rewriter.lazyEq.safeEq(elem, funAppRes)) // use lazy equality
          }

          nextState = nextState.updateArena(_.appendCell(BoolT1))
          val pred = nextState.arena.topCell.toNameEx

          val elemsInAndEq = funsetCdmElems.map(inAndEq)
          rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.or(elemsInAndEq: _*)))

          val dom = tla.apalacheSelectInSet(arg.toNameEx, funDom.toNameEx)
          tla.impl(dom, pred)
      }
    }

    nextState = nextState.updateArena(_.appendCell(BoolT1))
    val pred = nextState.arena.topCell
    val args = nextState.arena.getHas(funDom)
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toNameEx, tla.and(args.map(onPair): _*)))

    // S = DOMAIN f
    val domainEx = tla.eql(funsetDom.toNameEx, funDom.toNameEx)

    rewriter.rewriteUntilDone(
        nextState.setRex(
            tla.and(pred.toNameEx, domainEx)
        )
    )
  }
}

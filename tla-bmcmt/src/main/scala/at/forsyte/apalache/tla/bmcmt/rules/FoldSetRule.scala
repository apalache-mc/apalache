package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, RewritingRule, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.InlinerOfUserOper

class FoldSetRule(rewriter: SymbStateRewriter) extends RewritingRule {

  // expressions are transient, we don't need tracking
  private def mkInliner(decl: TlaOperDecl): InlinerOfUserOper =
    InlinerOfUserOper(BodyMapFactory.makeFromDecl(decl), new IdleTracker)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.foldSet, LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)), _, _) =>
        appName == operName && params.size == 2
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    // assume isApplicable
    case ex @ OperEx(ApalacheOper.foldSet, LetInEx(NameEx(_), opDecl), baseEx, setEx) =>
      // rewrite baseEx to its final cell form
      val baseState = rewriter.rewriteUntilDone(state.setRex(baseEx))
      val baseCell = baseState.asCell

      // rewrite setEx to its final cell form
      val setState = rewriter.rewriteUntilDone(baseState.setRex(setEx))
      val setCell = setState.asCell

      // Assume that setCell is in fact a Set-type cell
      val setMembers = setState.arena.getHas(setCell)

      // Now, we cache the set element equalities
      val postCacheState = cacheEqualityConstraints(setState, setMembers)

      // Then, we start the folding with the value of baseCell
      val initialState = postCacheState.setRex(baseCell.toNameEx)
      val foldResultType = baseCell.cellType

      val finalState = mkEq(foldResultType, setCell.toNameEx, opDecl)(Seq(), initialState, setMembers)
      finalState

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  // To guarantee evaluation uniqueness, we will need to compare cells.
  // To that end, we pre-cache equality constraints
  def cacheEqualityConstraints(initialState: SymbState, cells: Seq[ArenaCell]): SymbState = {
    val pairs = for {
      c1 <- cells
      c2 <- cells
      pa <- if (c1.id < c2.id) Some((c1, c2)) else None // skip ones where this is none
    } yield pa

    pairs.foldLeft(initialState) { case (state, (c1, c2)) =>
      rewriter.lazyEq.cacheOneEqConstraint(state, c1, c2)
    }
  }

  // Compares two cells belonging to the same set
  // a) they must belong to S (enough to check membership for one, if they are to be equal)
  // b) (lazy) equality must evaluate to true
  def eqToOther(setNameEx: TlaEx, thisCell: ArenaCell, otherCell: ArenaCell): TlaEx =
    tla.and(tla.in(otherCell.toNameEx, setNameEx), rewriter.lazyEq.safeEq(thisCell, otherCell))

  // convenience shorthand
  def solverAssert: TlaEx => Unit = rewriter.solverContext.assertGroundExpr

  // Generate a series of equations for fold. Similar to cardinality, we must track uniqueness.
  // Todo: rewrite this to a fold
  def mkEq(foldResultType: CellT, setNameEx: TlaEx, opDecl: TlaOperDecl)(counted: Seq[ArenaCell],
      partialState: SymbState, notCounted: Seq[ArenaCell]): SymbState = {
    notCounted match {
      case Nil => partialState // all counted!

      case hd +: tl =>
        val oldResultName = partialState.ex
        val arenaWithNewPartial = partialState.arena.appendCell(foldResultType)
        val newPartialResultCell = arenaWithNewPartial.topCell
        // newPartialResult = oldPartialResult if hd \notin set \/ \E c \in counted: hd = c /\ c \in set
        val arenaWithCondition = arenaWithNewPartial.appendCell(BoolT())
        val condCell = arenaWithCondition.topCell
        val condEx = tla.or(tla.notin(hd.toNameEx, setNameEx), tla.or(counted.map(eqToOther(setNameEx, hd, _)): _*))
        solverAssert(tla.eql(condCell.toNameEx, condEx))
        // newPartialResult = A(oldPartialResult, hd) otherwise
        val appEx = tla.appDecl(opDecl, oldResultName, hd.toNameEx)
        val inliner = mkInliner(opDecl)
        val inlinedEx = inliner.apply(appEx)
        // We now rewrite A(old, hd) to a cell
        val preInlineRewriteState = partialState.setArena(arenaWithCondition).setRex(inlinedEx)
        val postInlineRewriteState = rewriter.rewriteUntilDone(preInlineRewriteState)
        val inlinedAppEx = postInlineRewriteState.ex

        // We assert the condition implying the new value
        solverAssert(tla.eql(newPartialResultCell.toNameEx, tla.ite(condCell.toNameEx, oldResultName, inlinedAppEx)))

        val endState = postInlineRewriteState.setRex(newPartialResultCell.toNameEx)
        mkEq(foldResultType, setNameEx, opDecl)(hd +: counted, endState, tl)
    }
  }
}

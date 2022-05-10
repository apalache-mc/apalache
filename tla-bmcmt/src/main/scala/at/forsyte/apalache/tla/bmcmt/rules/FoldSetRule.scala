package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, RewritingRule, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.Inliner

/**
 * Rewriting rule for FoldSet. Similar to Cardinality, we need to consider element set presence and multiplicity.
 *
 * @author
 *   Jure Kukovec
 */
class FoldSetRule(rewriter: SymbStateRewriter, renaming: IncrementalRenaming) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.foldSet, LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)), _, _) =>
        appName == operName && params.size == 2
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    // assume isApplicable
    case OperEx(ApalacheOper.foldSet, LetInEx(NameEx(_), opDecl), baseEx, setEx) =>
      // rewrite baseEx to its final cell form
      val baseState = rewriter.rewriteUntilDone(state.setRex(baseEx))
      val baseCell = baseState.asCell

      // rewrite setEx to its final cell form
      val setState = rewriter.rewriteUntilDone(baseState.setRex(setEx))
      val setCell = setState.asCell
      val setNameEx = setCell.toNameEx

      // Assume that setCell is in fact a Set-type cell
      // getHas returns a sequence of cells the set cell points to
      // Notably, setCell may overapproximate, and not all elements pointed to
      // are set members, and some elements may be duplicated
      val setMembers = setState.arena.getHas(setCell).toArray

      // Now, we cache the set element equalities
      val postCacheState = cacheEqualityConstraints(setState, setMembers.toIndexedSeq)

      // Then, we start the folding with the value of baseCell
      val initialState = postCacheState.setRex(baseCell.toNameEx)

      // We need the type signature. The signature of FoldSet is
      // \A a,b : ((a,b) => a, a, Set(b)) => a
      // so the operator type must be (a,b) => a
      val a = baseEx.typeTag.asTlaType1()
      val b = setEx.typeTag.asTlaType1() match {
        case SetT1(bType) => bType
        case nonSet =>
          throw new TypingException(s"FoldSet argument $setEx should have the type Set(_), found $nonSet.", setEx.ID)
      }
      val opT = OperT1(Seq(a, b), a)
      // sanity check
      opDecl.typeTag.asTlaType1() match {
        case `opT` => // all good
        case badType =>
          val msg = s"FoldSet argument ${opDecl.name} should have the tag $opT, found $badType."
          throw new TypingException(msg, opDecl.ID)
      }

      // type aliases, because Builder
      val types = Map(
          "a" -> a,
          "b" -> b,
          "op" -> opT,
          "bool" -> BoolT1(),
      )

      // expressions are transient, we don't need tracking
      val inliner = new Inliner(new IdleTracker, renaming)
      // We can make the scope directly, since InlinePass already ensures all is well.
      val seededScope: Inliner.Scope = Map(opDecl.name -> opDecl)

      // To implement the FoldSet rule, we fold over the collection of set member cells.
      // At each one, we perform conditional application, i.e., the partial result is a cell that
      // equals the previous partial value, if
      // a) the current element does not belong to the set (overapproximation), or
      // b) the current element belongs to the set, but we have already visited another element
      //    that belonged to the set and had the same value (duplication)
      // otherwise, the nwe partial result is equal to the value of applying the operator
      // defined by `opDecl` to the previous partial result and the current cell.
      setMembers.zipWithIndex.foldLeft(initialState) { case (partialState, (currentCell, i)) =>
        // The collection of already visited cells, for equality asserts
        val counted = setMembers.take(i)
        // partialState currently holds the cell representing the previous application step
        val oldResultCellName = partialState.ex
        // if current \notin set (overapproximation), or
        // \E c \in counted: current = c /\ c \in set (duplication)
        // then newPartialResult = oldPartialResult
        val arenaWithCondition = partialState.arena.appendCell(BoolT1())
        val condCell = arenaWithCondition.topCell
        val condEx = tla
          .or(
              tla.not(tla.apalacheSelectInSet(currentCell.toNameEx, setNameEx) ? "bool") ? "bool",
              tla.or(counted.map(eqToOther(setNameEx, currentCell, _)).toIndexedSeq: _*) ? "bool",
          ) ? "bool"
        solverAssert(tla.eql(condCell.toNameEx, condEx).typed(types, "bool"))

        // otherwise newPartialResult = A(oldPartialResult, currentCell)
        // First, we inline the operator application, with cell names as parameters
        val appEx = tla.appOp(tla.name(opDecl.name) ? "op", oldResultCellName ? "a", currentCell.toNameEx ? "b")
        val inlinedEx = inliner.transform(seededScope)(appEx.typed(types, "a"))
        // We then rewrite A(oldPartial, currentCell) to a cell
        val preInlineRewriteState = partialState.setArena(arenaWithCondition).setRex(inlinedEx)
        val postInlineRewriteState = rewriter.rewriteUntilDone(preInlineRewriteState)
        val inlinedCellName = postInlineRewriteState.ex

        // The new cell value is an ITE, we let ITE rules handle the correct instantiation of
        // arenas for complex values
        val newPartialResultEx = tla
          .ite(
              condCell.toNameEx ? "bool",
              oldResultCellName ? "a",
              inlinedCellName ? "a",
          )
          .typed(types, "a")

        // Finally, we finish with a state containing the new cell expression
        val preITERewriteState = postInlineRewriteState.setRex(newPartialResultEx)
        rewriter.rewriteUntilDone(preITERewriteState)
      }

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  // To guarantee evaluation uniqueness, we will need to compare cells.
  // To that end, we pre-cache equality constraints
  def cacheEqualityConstraints(initialState: SymbState, cells: Seq[ArenaCell]): SymbState = {
    val pairs = for {
      c1 <- cells
      c2 <- cells
      pa <- if (c1.id < c2.id) Some((c1, c2)) else None // skip ones where this is None
    } yield pa

    pairs.foldLeft(initialState) { case (state, (c1, c2)) =>
      rewriter.lazyEq.cacheOneEqConstraint(state, c1, c2)
    }
  }

  // Compares two cells belonging to the same set. This function is only called where
  // `thisCell` can be assumed to already belong to `setNameEx`. Then, to check equality:
  // a) `otherCell` must also belong to `setNameEx`
  // b) (lazy) equality must evaluate to true
  def eqToOther(setNameEx: TlaEx, thisCell: ArenaCell, otherCell: ArenaCell): BuilderEx =
    tla.and(tla.apalacheSelectInSet(otherCell.toNameEx, setNameEx) ? "bool",
        rewriter.lazyEq.safeEq(thisCell, otherCell)) ? "bool"

  // convenience shorthand
  def solverAssert: TlaEx => Unit = rewriter.solverContext.assertGroundExpr
}

package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.rules.aux.SetOps
import at.forsyte.apalache.tla.bmcmt.{RewriterException, RewritingRule, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.Inliner
import at.forsyte.apalache.tla.types.tla

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

      // Assume that setCell is in fact a Set-type cell
      // getHas returns a sequence of cells the set cell points to
      // Notably, setCell may overapproximate, and not all elements pointed to
      // are set members, and some elements may be duplicated
      val setMembers = setState.arena.getHas(setCell).toArray

      // Find the non-duplicate predicates
      val (postCacheState, nonDups) = new SetOps(rewriter).dedup(setState, setCell)

      // Then, we start the folding with the value of baseCell
      val initialState = postCacheState.setRex(baseCell.toBuilder)

      // We need the type signature. The signature of FoldSet is
      // \A a,b : ((a,b) => a, a, Set(b)) => a
      // so the operator type must be (a,b) => a
      val a = TlaType1.fromTypeTag(baseEx.typeTag)
      val b = TlaType1.fromTypeTag(setEx.typeTag) match {
        case SetT1(bType) => bType
        case nonSet =>
          throw new TypingException(s"FoldSet argument $setEx should have the type Set(_), found $nonSet.", setEx.ID)
      }
      val opT = OperT1(Seq(a, b), a)
      val bool = BoolT1
      // sanity check
      TlaType1.fromTypeTag(opDecl.typeTag) match {
        case `opT` => // all good
        case badType =>
          val msg = s"FoldSet argument ${opDecl.name} should have the tag $opT, found $badType."
          throw new TypingException(msg, opDecl.ID)
      }

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
      setMembers.zip(nonDups).foldLeft(initialState) { case (partialState, (currentCell, isNonDup)) =>
        // partialState currently holds the cell representing the previous application step
        val oldResultCell = partialState.asCell
        // if currentCell does not belong to the set, or it is a duplicate,
        // then newPartialResult = oldPartialResult

        // otherwise newPartialResult = A(oldPartialResult, currentCell)
        // First, we inline the operator application, with cell names as parameters
        val appEx = tla.appOp(
            tla.name(opDecl.name, opT),
            oldResultCell.toBuilder,
            currentCell.toBuilder,
        )
        val inlinedEx = inliner.transform(seededScope)(appEx)
        // We then rewrite A(oldPartial, currentCell) to a cell
        val postInlineRewriteState = rewriter.rewriteUntilDone(partialState.setRex(inlinedEx))
        val inlinedCell = postInlineRewriteState.asCell

        // The new cell value is an ITE, we let ITE rules handle the correct instantiation of
        // arenas for complex values
        val newPartialResultEx = tla
          .ite(
              isNonDup.toBuilder,
              inlinedCell.toBuilder,
              oldResultCell.toBuilder,
          )

        // Finally, we finish with a state containing the new cell expression
        val preITERewriteState = postInlineRewriteState.setRex(newPartialResultEx)
        rewriter.rewriteUntilDone(preITERewriteState)
      }

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}

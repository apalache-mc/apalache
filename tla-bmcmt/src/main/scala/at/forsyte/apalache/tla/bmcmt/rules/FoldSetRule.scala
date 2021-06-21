package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, RewritingRule, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.InlinerOfUserOper

/**
 * <p>Rewriting rule for FoldSet.
 * Similar to Cardinality, we need to consider element set presence and multiplicity.
 *
 * @author Jure Kukovec
 */
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
      // getHas returns a sequence of cells the set cell points to
      // Notably, setCell may overapproximate, and not all elements pointed to
      // are set members, and some elements may be duplicated
      val setMembers = setState.arena.getHas(setCell)

      // Now, we cache the set element equalities
      val postCacheState = cacheEqualityConstraints(setState, setMembers)

      // Then, we start the folding with the value of baseCell
      val initialState = postCacheState.setRex(baseCell.toNameEx)

      // we need the type signature
      val a = baseEx.typeTag.asTlaType1()
      val b = setEx.typeTag.asTlaType1() match {
        case SetT1(bType) => bType
        case nonSet =>
          throw new TypingException(s"FoldSet argument $setEx should have the type Set[b], found $nonSet.")
      }
      mkEq(a, b, setCell.toNameEx, opDecl)(Seq(), initialState, setMembers)

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

  // Compares two cells belonging to the same set
  // a) they must belong to S (enough to check membership for one, if they are to be equal)
  // b) (lazy) equality must evaluate to true
  def eqToOther(setNameEx: TlaEx, thisCell: ArenaCell, otherCell: ArenaCell): BuilderEx =
    tla.and(tla.in(otherCell.toNameEx, setNameEx) ? "bool", rewriter.lazyEq.safeEq(thisCell, otherCell)) ? "bool"

  // convenience shorthand
  def solverAssert: TlaEx => Unit = rewriter.solverContext.assertGroundExpr

  // Generate a series of equations for fold. Similar to cardinality, we must track uniqueness.
  // TODO: rewrite this to a fold
  def mkEq(a: TlaType1, b: TlaType1, setNameEx: TlaEx, opDecl: TlaOperDecl)(counted: Seq[ArenaCell],
      partialState: SymbState, notCounted: Seq[ArenaCell]): SymbState = {
    notCounted match {
      case Nil => partialState // all counted!

      case hd +: tl =>
        // type aliases, because Builder
        val types = Map(
            "a" -> a,
            "b" -> b,
            "op" -> OperT1(Seq(a, b), a),
            "bool" -> BoolT1()
        )

        // partialState currently holds the cell representing the previous application step
        val oldResultCellName = partialState.ex
        // if hd \notin set (overapproximaiton) OR \E c \in counted: hd = c /\ c \in set (duplication)
        // then newPartialResult = oldPartialResult
        val arenaWithCondition = partialState.arena.appendCell(BoolT())
        val condCell = arenaWithCondition.topCell
        val condEx = tla
          .or(
              tla.notin(hd.toNameEx, setNameEx) ? "bool",
              tla.or(counted.map(eqToOther(setNameEx, hd, _)): _*) ? "bool"
          ) ? "bool"
        solverAssert(tla.eql(condCell.toNameEx, condEx).typed(types, "bool"))

        // otherwise newPartialResult = A(oldPartialResult, hd)
        // First, we inline the operator application, with cell names as parameters
        val appEx = tla.appOp(tla.name(opDecl.name) ? "op", oldResultCellName ? "a", hd.toNameEx ? "b")
        val inliner = mkInliner(opDecl)
        val inlinedEx = inliner.apply(appEx.typed(types, "a"))
        // We then rewrite A(old, hd) to a cell
        val preInlineRewriteState = partialState.setArena(arenaWithCondition).setRex(inlinedEx)
        val postInlineRewriteState = rewriter.rewriteUntilDone(preInlineRewriteState)
        val inlinedCellName = postInlineRewriteState.ex

        // The new cell value is an ITE, we let ITE rules handle the correct instantiation of
        // arenas for complex values
        val newParialResultEx = tla
          .ite(
              condCell.toNameEx ? "bool",
              oldResultCellName ? "a",
              inlinedCellName ? "a"
          )
          .typed(types, "a")

        // Finally, we recurse with a state containing the new cell expression
        val preITERewriteState = postInlineRewriteState.setRex(newParialResultEx)
        val endState = rewriter.rewriteUntilDone(preITERewriteState)
        mkEq(a, b, setNameEx, opDecl)(hd +: counted, endState, tl)
    }
  }
}

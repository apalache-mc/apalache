package at.forsyte.apalache.tla.bmcmt.stratifiedRules.bool

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{Rewriter, RewriterScope}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{addCell, StratifiedRule}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, TlaEx}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * Implements the rule for conjunction.
 *
 * If the `shortCircuit` flag is set to true, we translate A /\ B as IF A THEN B ELSE FALSE. Otherwise, we translate the
 * expression to an SMT conjunction.
 *
 * By default, short-circuiting is disabled.
 *
 * @author
 *   Jure Kukovec
 */
class AndStratifiedRule(rewriter: Rewriter, shortCircuit: Boolean = false)
    extends StratifiedRule[Option[TBuilderInstruction]] {
  private val simplifier = new ConstSimplifierForSmt()

  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(TlaBoolOper.and, _*) => true
    case _                           => false
  }

  override def buildArena(ex: TlaEx)(startingScope: RewriterScope): (
      RewriterScope,
      ArenaCell,
      Option[TBuilderInstruction]) = simplifier.simplifyShallow(ex) match {
    case OperEx(TlaBoolOper.and, args @ _*) =>
      if (args.isEmpty) {
        // empty conjunction is always true
        (startingScope, PureArena.cellTrue(startingScope.arena), None)
      } else {
        // use short-circuiting on state-level expressions (like in TLC)

        def toIte(es: Seq[TlaEx]): TBuilderInstruction = {
          // assume es is nonempty
          es.map(tla.unchecked).reduceRight[TBuilderInstruction] { case (elem, partial) =>
            tla.ite(elem, partial, PureArena.cellFalse(startingScope.arena).toBuilder)
          }
        }

        // no lazy short-circuiting: simply translate if-then-else to a chain of if-then-else expressions
        if (shortCircuit) {
          // create a chain of IF-THEN-ELSE expressions and rewrite them
          val (scope, cell) = rewriter.rewrite(toIte(args))(startingScope)
          (scope, cell, None)
        } else {
          // simply translate to a conjunction
          val (arenaWithAndCell, andCell) = addCell(startingScope.arena, BoolT1)

          val (newScope, rewrittenArgCells) =
            // With AND all blocks belong to the same scope, so we have to propagate it
            args.foldLeft((startingScope.copy(arena = arenaWithAndCell), Seq.empty[TBuilderInstruction])) {
              case ((scope, cellSeq), term) =>
                val (newScope, termCell) = rewriter.rewrite(term)(scope)
                (newScope, cellSeq :+ termCell.toBuilder)
            }

          (newScope, andCell, Some(tla.and(rewrittenArgCells: _*)))
        }
      }

    case e @ _ =>
      // the simplifier has rewritten the conjunction to some other expression
      val (scope, cell) = rewriter.rewrite(e)(startingScope)
      (scope, cell, None)
  }

  override def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: Option[TBuilderInstruction]): Unit = {
    // Only add constraints, if ITE rewriting didn't fire (in that case, the ITE rule does it for us)
    auxData.foreach { conjunction =>
      rewriter.assert(tla.eql(cell.toBuilder, conjunction))
    }
  }
}

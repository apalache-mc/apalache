package at.forsyte.apalache.tla.bmcmt.stratifiedRules.base

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.IntValueCache
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{Rewriter, RewriterScope, StratifiedRule}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * Rewrites integer constants.
 *
 * @author
 *   Jure Kukovec
 */
class IntConstStratifiedRule(rewriter: Rewriter, intValueCache: IntValueCache) extends StratifiedRule[BigInt] {

  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case ValEx(TlaInt(_)) => true
    case _                => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, BigInt) = ex match {
    case ValEx(TlaInt(n)) =>
      val (newArena, cell) = intValueCache.getOrCreate(startingScope.arena, n)
      (startingScope.copy(arena = newArena), cell, n)

    case _ =>
      throw new RewriterException(getClass.getSimpleName + " is not applicable", ex)
  }

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: BigInt): Unit = {
    rewriter.assert(tla.eql(cell.toBuilder, tla.int(auxData)))
  }

}

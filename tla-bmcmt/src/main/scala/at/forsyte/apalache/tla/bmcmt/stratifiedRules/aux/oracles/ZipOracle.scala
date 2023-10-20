package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * [[ZipOracle]] is an optimization of [[Oracle]]. It groups several values of the background oracle together, in order
 * to reduce the number of constraints. In this sense, it compresses several oracle values into one. As a consequence,
 * [[CherryPick]] pick constructs significantly fewer constants and constraints. It is up to the user of [[ZipOracle]]
 * to make sure that the grouped values may be treated as equivalent.
 *
 * @param backOracle
 *   the background oracle whose values are grouped together
 * @param groups
 *   A list of groups over the indices of the background oracle. Indices within each group must be sorted, as the
 *   sorting determines the order of generated SMT constraints; see
 *   https://github.com/informalsystems/apalache/issues/2120.
 */
class ZipOracle(backOracle: Oracle, groups: Seq[Seq[Int]]) extends Oracle {
  override def size: Int = groups.size

  override def chosenValueIsEqualToIndexedValue(scope: RewriterScope, index: BigInt): TBuilderInstruction =
    if (groups.indices.contains(index)) {
      val conds = groups(index.toInt).map(i => backOracle.chosenValueIsEqualToIndexedValue(scope, i))
      tla.or(conds: _*)
    } else tla.bool(false)

  def getIndexOfChosenValueFromModel(solverContext: SolverContext): BigInt = {
    val backIndex = backOracle.getIndexOfChosenValueFromModel(solverContext)
    groups.indexWhere(_.contains(backIndex))
  }
}

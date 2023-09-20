package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * Given an `oracle` and a set `values` of size `N`, such that {{{values \subseteq {0,...,oracle.size},}}} a
 * `SparseOracle` `o` acts as a compression of `oracle` with `o.size = N`, such that for any scope `s` and any element
 * `i \in values`, the following holds:
 * {{{o.chosenValueIsEqualToIndexedValue(s,indexOf(i)) = oracle.chosenValueIsEqualToIndexedValue(s,i),}}} where
 * `indexOf` is a bijective mapping from `values` to `{0,..., N}`.
 *
 * @author
 *   Jure Kukovec
 *
 * @param oracle
 *   the backend oracle that ranges over values 0..|S|-1
 * @param values
 *   the set S of oracle values
 */
class SparseOracle(oracle: Oracle, val values: Set[Int]) extends Oracle {
  private[oracles] val sortedValues: Seq[Int] = values.toSeq.sorted

  override def size: Int = values.size

  def chosenValueIsEqualToIndexedValue(scope: RewriterScope, index: BigInt): TBuilderInstruction =
    sortedValues
      .map { oracle.chosenValueIsEqualToIndexedValue(scope, _) }
      .applyOrElse[Int, TBuilderInstruction](index.toInt, _ => tla.bool(false))

  override def caseAssertions(
      scope: RewriterScope,
      assertions: Seq[TBuilderInstruction],
      elseAssertionsOpt: Option[Seq[TBuilderInstruction]] = None): TBuilderInstruction =
    oracle.caseAssertions(scope, assertions, elseAssertionsOpt)

  override def getIndexOfChosenValueFromModel(solverContext: SolverContext): BigInt = {
    val rawIdx: Int = oracle.getIndexOfChosenValueFromModel(solverContext).toInt
    sortedValues.indexOf(rawIdx)
  }
}

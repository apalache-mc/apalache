package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}

/**
 * Given a set `indices` of size `N`, sparse oracle is able to answer {{{chosenValueIsEqualToIndexedValue(_, i),}}} for
 * any `i \in indices`, despite having a size, which may be smaller than some (ot all) elements of `indices`.
 * {{{chosenValueIsEqualToIndexedValue(_, j),}}} for any `j` not in `indices` does not hold.
 *
 * Internally, every SparseOracle `s` maintains an oracle `o` of size `N-1`, such that for every scope `X`, and any
 * index `i \in indices` the following holds:
 * {{{s.chosenValueIsEqualToIndexedValue(X,i) = o.chosenValueIsEqualToIndexedValue(x, idxMap(i),}}} where `idxMap` is
 * some bijection from `indices` to `{0,...,N-1}`.
 *
 * @author
 *   Jure Kukovec
 *
 * @param mkOracle
 *   the method to create the backend oracle, of a given size
 * @param values
 *   the set S of oracle values
 */
class SparseOracle(mkOracle: Int => Oracle, val values: Set[Int]) extends Oracle {
  private[oracles] val oracle = mkOracle(values.size)
  private[oracles] val sortedValues: Seq[Int] = values.toSeq.sorted
  private[oracles] val indexMap: Map[Int, Int] = Map(sortedValues.zipWithIndex: _*)

  override def size: Int = values.size

  def chosenValueIsEqualToIndexedValue(scope: RewriterScope, index: BigInt): BuilderT =
    indexMap
      .get(index.toInt)
      .map {
        oracle.chosenValueIsEqualToIndexedValue(scope, _)
      }
      .getOrElse(tla.bool(false))

  override def caseAssertions(
      scope: RewriterScope,
      assertions: Seq[BuilderT],
      elseAssertionsOpt: Option[Seq[BuilderT]] = None): BuilderT =
    oracle.caseAssertions(scope, assertions, elseAssertionsOpt)

  override def getIndexOfChosenValueFromModel(solverContext: SolverContext): BigInt = {
    val oracleIdx = oracle.getIndexOfChosenValueFromModel(solverContext).toInt
    sortedValues.applyOrElse[Int, Int](oracleIdx, _ => -1)
  }
}

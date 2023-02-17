package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.SymbState
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import com.typesafe.scalalogging.LazyLogging

/**
 * The oracle for sparse values, that is, a set S of naturals. This oracle is mapped on a smaller contiguous range
 * 0..|S|-1.
 *
 * @author
 *   Igor Konnov
 *
 * @param oracle
 *   the backend oracle that ranges over values 0..|S|-1
 * @param values
 *   the set S of oracle values
 */
class SparseOracle(oracle: Oracle, val values: Set[Int]) extends Oracle with LazyLogging {
  // a reverse mapping from elements to their indices in the sorted sequence of the elements of S
  private val sortedValues: Seq[Int] = values.toSeq.sorted
  private val indexMap: Map[Int, Int] = Map(sortedValues.zipWithIndex: _*)

  override def size: Int = values.size

  override def whenEqualTo(state: SymbState, position: Int): TBuilderInstruction = {
    assert(indexMap.contains(position))
    oracle.whenEqualTo(state, indexMap(position))
  }

  override def caseAssertions(
      state: SymbState,
      assertions: Seq[TBuilderInstruction],
      elseAssertions: Seq[TBuilderInstruction] = Seq.empty): TBuilderInstruction =
    oracle.caseAssertions(state, assertions, elseAssertions)

  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    val rawPos = oracle.evalPosition(solverContext, state)
    logger.info(s"rawPos = ${rawPos}, ${oracle.getClass}")
    assert(sortedValues.isDefinedAt(rawPos))
    sortedValues(rawPos)
  }
}

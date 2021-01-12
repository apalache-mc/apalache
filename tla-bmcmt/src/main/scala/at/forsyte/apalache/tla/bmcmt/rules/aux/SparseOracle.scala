package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.SymbState
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * The oracle for sparse values, that is, a set S of naturals.
  * This oracle is mapped on a smaller contiguous range 0..|S|-1.
  *
  * @author Igor Konnov
  *
  * @param oracle the backend oracle that ranges over values 0..|S|-1
  * @param values the set S of oracle values
  */
class SparseOracle(oracle: Oracle, val values: Set[Int]) extends Oracle {
  // a reverse mapping from elements to their indices in the sorted sequence of the elements of S
  private val sortedValues: Seq[Int] = values.toSeq.sorted
  private val indexMap: Map[Int, Int] = Map(sortedValues.zipWithIndex :_*)

  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state    a symbolic state
    * @param position a position the oracle should be equal to
    */
  override def whenEqualTo(state: SymbState, position: Int): TlaEx = {
    assert(indexMap.contains(position))
    oracle.whenEqualTo(state, indexMap(position))
  }

  /**
    * Produce a ground expression that contains assertions for the possible oracle values.
    *
    * @param state      a symbolic state
    * @param assertions a sequence of assertions, one per oracle value
    * @return an expression ite(oracle = 0, ite(oracle = 1, ...))
    */
  override def caseAssertions(state: SymbState, assertions: Seq[TlaEx]): TlaEx = {
    oracle.caseAssertions(state, assertions)
  }

  /**
    * Get a symbolic state and decode the value of the oracle variable into an integer.
    * This method assumes that the solver context has produced an SMT model.
    *
    * @param solverContext a solver context
    * @param state         a symbolic state
    * @return an integer value of the oracle
    */
  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    val rawPos = oracle.evalPosition(solverContext, state)
    assert(sortedValues.isDefinedAt(rawPos))
    sortedValues(rawPos)
  }
}

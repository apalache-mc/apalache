package at.forsyte.apalache.tla.bmcmt

/**
  * At this point, symbolic search was split (by a disjunction A1 \/ ... \/ An).
  * We save the search state and the number of branches that have been already explored.
  *
  * @param state the state in which the branching has occurred
  * @param numBranches the number of branches to explore
  * @param solverContextLevel the number of context pushes made by the SMT solver before exploring the branches,
  *                           we use it to pop the SMT contexts that were introduced by the branches.
  */
class Branchpoint(val state: SymbState,
                  val numBranches: Int,
                  val solverContextLevel: Int) {
  /**
    * The number of explored branches (assuming that we can order the branches).
    */
  var exploredBranchesCnt: Int = 0
}

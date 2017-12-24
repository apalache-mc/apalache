package at.forsyte.apalache.tla.bmcmt

/**
  * A branching point in the symbolic search. TLA+ specification may encode several symbolic transitions
  * leading to different variable assignments
  * (e.g., x' = y \/ x' = z gives us two symbolic transitions x' = y and x' = z).
  * After making a single step encoded by Next, we have to choose between the possible symbolic transitions.
  * A branching point is one such a choice that saves the symbolic state to be evaluated
  * and the level in the SMT context stack. After restoring the SMT context to solverContextLevel, we can evaluate
  * the state.
  *
  * @param state              the state in which the branching has occurred
  * @param depth              the search depth reached so far (an initial state has depth 0)
  * @param contextLevel the number of context pushes made by the SMT solver before exploring the branches,
  *                           we use it to pop the SMT contexts that were introduced by the branches.
  * @author Igor Konnov
  */
class Branchpoint(val state: SymbState,
                  val depth: Int,
                  val contextLevel: Int) {
}

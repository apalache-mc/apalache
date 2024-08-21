package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}

/**
 * <p>A small collection of operations on sets that can be reused by rewriting rules.</p>
 *
 * @param rewriter
 *   state rewriter
 * @author
 *   Igor Konnov
 */
class SetOps(rewriter: SymbStateRewriter) {

  /**
   * Considering the cells `c[1], ..., c[n]` as a sequence of elements connected to `S`, produce a sequence of Boolean
   * cells `b[1], ..., b[n]` that have the following property for i \in 1..n:
   * {{{
   *   b[i] <=>
   *     /\ c[i] \in S
   *     /\ \A j \in 1..(i - 1):
   *           ~b[j] \/ c[j] /= c[i]
   * }}}
   *
   * @param state
   *   a symbolic state to start with
   * @param oldSet
   *   a set cell to transform
   * @return
   *   a new symbolic state and the sequence of Boolean cells
   */
  def dedup(state: SymbState, oldSet: ArenaCell): (SymbState, Seq[ArenaCell]) = {
    rewriter.solverContext.log(s";DEDUP $oldSet {")
    val elems = state.arena.getHas(oldSet)
    var newArena = state.arena
    // introduce one predicate per element
    val predicates = elems.map { _ =>
      newArena = newArena.appendCell(BoolT1)
      newArena.topCell
    }
    var nextState = state.setArena(newArena)
    // Cache equality constraints. In the worst case, there are N^2 / 2 of them.
    for (l <- elems) {
      for (r <- elems) {
        if (l.id < r.id) {
          nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, l, r)
        }
      }
    }
    // Enforce equality via propositional variables. This is sound in the OOPSLA19 encoding, but may fail for arrays.
    // Generate a series of equations. There are O(N^2) constraints.
    for (((c_i, b_i), i) <- elems.zip(predicates).zipWithIndex) {
      // b[i] <=>
      //   /\ c[i] \in S
      //   /\ \A j \in 0..(i - 1):
      //      ~b[j] \/ c[j] /= c[i]
      def notSeen(j: Int): BuilderT = {
        tla.or(tla.not(predicates(j).toBuilder), tla.not(tla.eql(c_i.toBuilder, elems(j).toBuilder)))
      }

      val rhs = tla.and(tla.selectInSet(c_i.toBuilder, oldSet.toBuilder), tla.and(0.until(i).map(notSeen): _*))
      rewriter.solverContext.assertGroundExpr(tla.eql(b_i.toBuilder, rhs))
    }

    rewriter.solverContext.log(";} DEDUP ")
    (nextState, predicates)
  }
}

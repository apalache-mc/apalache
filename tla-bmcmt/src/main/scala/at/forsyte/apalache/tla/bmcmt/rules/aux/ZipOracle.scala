package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.SymbState
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx}

/**
 * [[ZipOracle]] is an optimization of [[Oracle]]. It groups several values of the background oracle together, in
 * order to reduce the number of constraints. It is up to the user of {{{ZipOracle}}} to make sure that the grouped
 * values may be treated as equivalent.
 *
 * @param backOracle
 *   the background oracle whose values are grouped together
 * @param groups
 *   a list of groups over the values of the background oracle
 */
class ZipOracle(backOracle: Oracle, groups: List[Set[Int]]) extends Oracle {
  override def size: Int = groups.size

  override def whenEqualTo(state: SymbState, position: Int): TlaEx = {
    assert(position < groups.size)
    val conds = groups(position).map(index => tla.fromTlaEx(backOracle.whenEqualTo(state, index))).toList
    tla.or(conds: _*).as(BoolT1())
  }

  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    val backIndex = backOracle.evalPosition(solverContext, state)
    groups.indexWhere(_.contains(backIndex))
  }
}

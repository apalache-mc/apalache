package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.SymbState
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.TlaControlOper

/**
 * An abstract version of an oracle that is used e.g. in CherryPick.
 *
 * @author
 *   Igor Konnov
 */
trait Oracle extends Serializable {

  /**
   * The number of values that this oracle is defined over: `0..(size - 1)`.
   *
   * @return
   *   the number of values
   */
  def size: Int

  /**
   * Produce an expression that states that the oracle values equals to the given integer position. The actual
   * implementation may be different from an integer comparison.
   *
   * @param state
   *   a symbolic state
   * @param position
   *   a position the oracle should be equal to
   */
  def whenEqualTo(state: SymbState, position: Int): TlaEx

  /**
   * Produce a ground expression that contains assertions for the possible oracle values.
   *
   * @param state
   *   a symbolic state
   * @param assertions
   *   a sequence of assertions, one per oracle value
   * @param elseAssertions
   *   an optional sequence of assertions, one per oracle value
   * @return
   *   an expression ite(oracle = 0, ite(oracle = 1, ...))
   */
  def caseAssertions(state: SymbState, assertions: Seq[TlaEx], elseAssertions: Seq[TlaEx] = Seq()): TlaEx = {
    size match {
      case 0 => state.arena.cellTrue().toNameEx

      case 1 => assertions.head

      case _ =>
        // iteCases is a sequence of tuples, with the 1st and 2nd elements of each tuple being the "if" and "else" cases of an ite.
        // If elseAssertions is not empty, each tuple has its 1st element from assertions and its 2nd form elseAssertions.
        // If elseAssertions is empty, each tuple has its 1st element from assertions and its 2nd defaults to "ValEx(TlaBool(true))".
        val iteCases = assertions.zipAll(elseAssertions, tla.bool(true).typed(), tla.bool(true).typed())
        val es =
          iteCases.slice(0, size).zipWithIndex.map { case (e, i) =>
            val ex = OperEx(TlaControlOper.ifThenElse, whenEqualTo(state, i), e._1, e._2)(e._1.typeTag)
            tla.fromTlaEx(ex)
          }
        tla.and(es: _*).as(BoolT1)
    }
  }

  /**
   * Get a symbolic state and decode the value of the oracle variable into an integer. This method assumes that the
   * solver context has produced an SMT model.
   *
   * @param solverContext
   *   a solver context
   * @param state
   *   a symbolic state
   * @return
   *   an integer value of the oracle
   */
  def evalPosition(solverContext: SolverContext, state: SymbState): Int
}

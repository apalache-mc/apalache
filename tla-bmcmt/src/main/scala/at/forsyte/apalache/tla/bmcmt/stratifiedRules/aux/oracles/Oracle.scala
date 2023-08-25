package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * An oracle provides a means of choosing a single value, out of a finite collection of candidate values. It can
 * generate SMT constraints, which capture the conditions under which the chosen value may/must be equal to the
 * candidate values.
 *
 * For the purposes of describing the oracle's behavior, we can assume that there are `N` distinct possible values,
 * which are indexed with `0,1,2,...,N-1` (though they need not be represented as such in the implementation). We refer
 * to the `i`-th candidate value as `vi`.
 *
 * @author
 *   Jure Kukovec
 */
trait Oracle {

  /**
   * The number of values that this oracle is defined over: `0..(size - 1)`.
   */
  def size: Int

  /**
   * Produce an expression that states that the chosen value equals to the value `v_{index}`. The actual implementation
   * may be different from an integer comparison.
   */
  def oracleValueIsEqualToIndexedValue(scope: RewriterScope, index: Int): TBuilderInstruction

  /**
   * Produce a ground expression that contains assertions for the possible oracle values.
   *
   * The `assertions` sequence must contain `N` elements, where `N` equals the number of oracle value candidates. The
   * `i`-th element of `assertions` describes a formula, which holds if the oracle value is equal to the `i`-th
   * candidate value `vi`.
   *
   * Optionally, a sequence option `elseAssertionsOpt`, containing a sequence of the same length as assertions`, may be
   * provided. If it is, the `i`-th element of the sequence describes a formula, which holds if the oracle value is
   * _not_ equal to the `i`-th candidate value `vi`. If this value is not provided, a default sequence, containing `N`
   * copies of `TRUE` is taken in place of the aforementioned formulas.
   */
  def caseAssertions(
      scope: RewriterScope,
      assertions: Seq[TBuilderInstruction],
      elseAssertionsOpt: Option[Seq[TBuilderInstruction]] = None): TBuilderInstruction = {
    if (assertions.size != this.size || elseAssertionsOpt.exists { _.size != this.size })
      throw new IllegalStateException(s"Invalid call to Oracle, assertion sequences must have length $size.")

    size match {
      // If the oracle has no candidate values, then caseAssertions should return a no-op for SMT, i.e. TRUE.
      case 0 => PureArena.cellTrue(scope.arena).toBuilder

      // If the oracle has a single candidate value, then the chosen value will always equal to the (sole) candidate value.
      // In other words, for such an oracle, whenEqualTo(..., 0) will always hold.
      // Therefore, we don't need an ITE (and don't need to consider elseAssertions), we just take the first assertion.
      case 1 => assertions.head

      case _ =>
        val elseAssertions = elseAssertionsOpt.getOrElse(Seq.fill(size)(tla.bool(true)))
        // We zip a sequence of tuples, with the 1st and 2nd elements of each tuple being the "then" and "else" cases of an ite.
        // If elseAssertionsOpt is not empty, each tuple has its 1st element from assertions and its 2nd form elseAssertionsOpt.
        // If elseAssertionsOpt is empty, each tuple has its 1st element from assertions and its 2nd defaults to TRUE.
        tla.and(
            assertions.zip(elseAssertions).zipWithIndex.map { case ((thenFormula, elseFormula), i) =>
              tla.ite(oracleValueIsEqualToIndexedValue(scope, i), thenFormula, elseFormula)
            }: _*
        )
    }
  }

  /**
   * Decode the value of the oracle variable into an integer index. This method assumes that the solver context has
   * produced an SMT model.
   */
  def getIndexOfOracleValueFromModel(solverContext: SolverContext): Int
}

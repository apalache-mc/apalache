package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * An oracle that always has the same value. This class specializes all methods to the case oracle == fixedValue.
 * However, evalPosition always returns fixedValue.
 *
 * @param fixedValue
 *   a fixed value of the oracle
 */
class MockOracle(fixedValue: Int) extends Oracle {
  require(fixedValue >= 0, "MockOracle must have a non-negative fixed value.")

  override def size: Int = fixedValue + 1

  override def chosenValueIsEqualToIndexedValue(scope: RewriterScope, index: BigInt): TBuilderInstruction =
    tla.bool(index == fixedValue)

  override def caseAssertions(
      scope: RewriterScope,
      assertions: Seq[TBuilderInstruction],
      elseAssertionsOpt: Option[Seq[TBuilderInstruction]] = None): TBuilderInstruction = {
    require(assertions.size == this.size && elseAssertionsOpt.forall { _.size == this.size },
        s"Invalid call to Oracle, assertion sequences must have length $size.")
    assertions(fixedValue)
  }

  override def getIndexOfChosenValueFromModel(solverContext: SolverContext): BigInt =
    fixedValue
}

object MockOracle {
  def create(fixedValue: Int): MockOracle = new MockOracle(fixedValue)
}

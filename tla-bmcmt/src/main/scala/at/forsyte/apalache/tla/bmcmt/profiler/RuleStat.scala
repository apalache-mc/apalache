package at.forsyte.apalache.tla.bmcmt.profiler

/**
 * Statistics per rewriting rule.
 *
 * @param ruleName the name of the used rule
 *
 * @author Igor Konnov
 */
class RuleStat(val ruleName: String) {

  /**
   * The number of times the rewriting rule is called by SymbStateRewriterImpl.
   */
  var nCalls: Long = 0

  /**
   * The number of SMT constants that are introduced by the rule itself.
   */
  var nSmtConstsSelf = 0

  /**
   * The number of arena cells that are introduced by the rule itself.
   */
  var nCellsSelf = 0

  /**
   * The number of SMT assertions that are made by the rule itself (not its subrules).
   */
  var nSmtAssertsSelf = 0

  /**
   * The total length of SMT assertions that are made by the rule itself.
   * The division smtAssertsLenTotal / nSmtAssertsSelf gives us the average length of clauses.
   */
  var smtAssertsSizeTotal: Long = 0

  /**
   * The average size of smt assertions
   * @return the average size
   */
  def smtAssertsSizeAvg: Long = if (nSmtAssertsSelf > 0) smtAssertsSizeTotal / nSmtAssertsSelf else 0
}

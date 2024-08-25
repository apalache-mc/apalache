package at.forsyte.apalache.tla.bmcmt

/**
 * <p>The collection of all magic constants that are used in the rewriting process.</p>
 *
 * <p>TODO: move to RewriterConfig?</p>
 */
object Limits {

  /**
   * The upper bound on the size of the Cartesian product
   */
  val MAX_PRODUCT_SIZE = 1000000

  /**
   * An upper bound on the size of a base set that is expanded to a powerset, currently, `20`.
   */
  val POWSET_MAX_BASE_SIZE = 20

  /**
   * An upper bound on the number of rewriting steps that are applied to the same rule.
   */
  val RECURSION_LIMIT: Int = 10000

}

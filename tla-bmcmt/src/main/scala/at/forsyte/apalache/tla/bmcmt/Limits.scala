package at.forsyte.apalache.tla.bmcmt

/**
  * The collection of all magic constants that are used in the rewriting process.
  */
object Limits {
  /**
    * The upper bound on the size of the Cartesian product
    */
  val MAX_PRODUCT_SIZE = 1000000

  /**
    * An upper bound on the size of an explicitely constructed powerset.
    */
  val POWSET_MAX_SIZE = 1000000

  /**
    * An upper bound on the number of rewriting steps that are applied to the same rule.
    */
  val RECURSION_LIMIT: Int = 10000

}

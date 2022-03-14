package at.forsyte.apalache.tla.lir

/**
 * Convenient shortcuts and definitions, mostly used in tests. Import them, when needed.
 */
package object convenience {

  /**
   * This is just a short-hand to Builder, so one can type more naturally, e.g., tla.plus(tla.int(2), tla.int(3))
   */
  val tla: Builder = new Builder()
}

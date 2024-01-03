package at.forsyte.apalache.tla.lir

/**
 * Convenient shortcuts and definitions, mostly used in tests. Import them, when needed.
 */
package object convenience {

  /**
   * A short-hand to the instance of Builder, so one can type more naturally, e.g.:
   *
   * {{{
   * tla.plus(tla.int(2), tla.int(3))
   * }}}
   *
   * Alternatively, you can import all of its methods via:
   *
   * {{{
   * import at.forsyte.apalache.tla.lir.convenience.tla._
   * }}}
   *
   * <b>Warning:</b> you should prefer using the instance of the typed builder, which is accessible via
   * `at.forsyte.apalache.tla.types.tla`` in the package `tla-types`.
   */
  val tla: Builder = new Builder()
}

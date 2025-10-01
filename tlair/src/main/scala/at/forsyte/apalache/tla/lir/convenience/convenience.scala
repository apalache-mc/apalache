package at.forsyte.apalache.tla.lir

/**
 * Convenient shortcuts and definitions, mostly used in tests. Import them, when needed.
 *
 * <b>This package is deprecated</b>. Use the typed builder in `at.forsyte.apalache.tla.types.tla` instead.
 */
package object convenience {

  /**
   *
   * <b>Deprecation warning:</b> If you are writing new code, use the typed builder:
   *
   * {{{
   * import at.forsyte.apalache.tla.types.tla
   *
   * tla.plus(tla.int(2), tla.int(3))
   * }}}
   *
   * <b>Legacy documentation:</b> A short-hand to the instance of Builder, so one can type more naturally, e.g.:
   *
   * {{{
   * import at.forsyte.apalache.tla.lir.convenience.tla
   * tla.plus(tla.int(2), tla.int(3))
   * }}}
   *
   * Alternatively, you can import all of its methods via:
   *
   * {{{
   * import at.forsyte.apalache.tla.lir.convenience.tla._
   * }}}
   */
  val tla: Builder = new Builder()
}

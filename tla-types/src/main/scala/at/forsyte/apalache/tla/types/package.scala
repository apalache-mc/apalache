package at.forsyte.apalache.tla

package object types {

  import at.forsyte.apalache.tla.typecomp._

  /**
   * A short-hand to the instance of the typed builder, so one can easily construct expressions. For example:
   *
   * {{{
   * import at.forsyte.apalache.tla.types._
   *
   * test("tla builder succeeds") {
   *   val ex: TlaEx = tla.plus(tla.int(2), tla.int(3))
   *   assert(ex.isInstanceOf[OperEx])
   * }
   * }}}
   *
   * Alternatively, you can import all of its methods via:
   *
   * {{{
   * // import implicit conversions
   * import at.forsyte.apalache.tla.types._
   * // import the names from the tla object
   * import at.forsyte.apalache.tla.types.tla._
   * }}}
   *
   * For the implementation details, see [[ScopedBuilder]].
   */
  val tla: ScopedBuilder = new ScopedBuilder()
}

package at.forsyte.apalache.tla

/**
 * Defines a premade instance of [[at.forsyte.apalache.tla.typecomp.ScopedBuilder ScopedBuilder]], named [[tla]].
 *
 * =Importing and using [[tla]]=
 *
 * The [[tla]] object provides a convenient interface for constructing type- and scope-correct TLA+ expressions. It
 * exposes methods that correspond to TLA+ operators, for example:
 * {{{
 *  val ex: TlaEx = tla.plus(tla.int(2), tla.int(3))
 * }}}
 *
 * You can access it by importing via
 * {{{
 * import at.forsyte.apalache.tla.types._
 * }}}
 * It is recommended to import the entire package, instead of just
 * {{{
 * import at.forsyte.apalache.tla.types.tla
 * }}}
 * to enable the implicit conversions described below:
 *
 * All [[tla]] ([[at.forsyte.apalache.tla.typecomp.ScopedBuilder ScopedBuilder]]) methods return
 * [[at.forsyte.apalache.tla.typecomp.TBuilderInstruction TBuilderInstruction]] or
 * [[at.forsyte.apalache.tla.typecomp.TBuilderOperDeclInstruction TBuilderOperDeclInstruction]] values, not
 * [[at.forsyte.apalache.tla.lir TlaEx]] or [[at.forsyte.apalache.tla.lir.TlaOperDecl TlaOperDecl]] values (see
 * [[typecomp]] for a more elaborate explanation).
 *
 * Given a value `v: TBuilderInternalState` (the case for `TBuilderOperDeclInstruction` is analogous), we have to
 * convert it to the associated `TlaEx` in any of the equivalent ways listed below. One can think of `v` as a process to
 * obtain a `TlaEx` value, rather than the value itself.
 * {{{
 *   val tlaEx: TlaEx = v
 *   val tlaEx = build(v)
 *   val tlaEx = v.build
 * }}}
 * Here, `build` is an implicit `TBuilderInstruction => TlaEx` conversion defined in [[typecomp]]. The same package
 * defines an implicit class, with a `_.build` method, so `build` may be used as a suffix-call to
 * `TBuilderInstruction`s. These implicits get imported alongside [[tla]] with
 * {{{
 * import at.forsyte.apalache.tla.types._
 * }}}
 *
 * Sometimes it is convenient to import all method names, to avoid typing `tla.x(tla.y(...)))`. In that case, simply add
 * {{{
 * import at.forsyte.apalache.tla.types.tla._
 * }}}
 *
 * Example:
 * {{{
 * import at.forsyte.apalache.tla.types._
 *
 * test("tla builder succeeds") {
 *   val ex: TlaEx = tla.plus(tla.int(2), tla.int(3))
 *   assert(ex.isInstanceOf[OperEx])
 * }
 * }}}
 * or, when using method names directly
 * {{{
 * import at.forsyte.apalache.tla.types._
 * import at.forsyte.apalache.tla.types.tla._
 *
 * test("invariant") {
 *   // (\E x \in S: TRUE) <=> (S /= {})
 *   val inv: TlaEx =
 *     equiv(
 *       exists(
 *         name("x", IntT1),
 *         name("S", SetT1(IntT1)),
 *         bool(true)
 *       ),
 *       neql(
 *         name("S", SetT1(IntT1)),
 *         emptySet(IntT1)
 *       )
 *     )
 *   ...
 * }
 * }}}
 *
 * =Exceptions=
 *
 * There are three categories of exceptions, which you may encounter when using [[tla]]:
 *
 * <ul>
 *
 * <li> [[typecomp.TBuilderTypeException TBuilderTypeException]]: This exception indicates that one or more arguments
 * have incorrect types, w.r.t. the operator. For example, attempting to construct `1 + "a"` would yield this exception:
 * {{{
 *   val ex: TlaEx = tla.plus(tla.int(1), tla.str("a")) // throws TBuilderTypeException
 * }}}
 * as `+` requires two arguments of type `Int`. </li>
 *
 * <li> `IllegalArgumentException`: This exception indicates that one or more arguments has an illegal shape, w.r.t. the
 * operator, or that the number of arguments is incorrect. Some operators require e.g. `ValEx(TlaStr(_))` values
 * specifically, instead of just `Str`-typed values (for instance keys in
 * [[typecomp.ScopedBuilder.rec the record constructor]]). Other operators are variadic, but require the number of
 * arguments to be of a specific parity (e.g. [[typecomp.ScopedBuilder.funDefMixed funDefMixed]]), or require a positive
 * number of arguments (e.g. [[typecomp.ScopedBuilder.enumSet enumSet]]). Example:
 * {{{
 *   val ex: TlaEx = tla.enumSet() // throws IllegalArgumentException
 * }}}
 * would throw an `IllegalArgumentException`, as [[typecomp.ScopedBuilder.enumSet enumSet]] requires a strictly positive
 * number of arguments ([[typecomp.ScopedBuilder.emptySet emptySet]] should have been used in this case). </li>
 *
 * <li> [[typecomp.TBuilderScopeException TBuilderScopeException]]: This exception indicates that a variable is used
 * with different types in the same scope, or that shadowing has occurred. Example:
 * {{{
 *   // x > 1 /\ x /= "1"
 *   // throws a TBuilderScopeException
 *   val ex: TlaEx =
 *     tla.and(
 *       tla.ge(
 *         tla.name("x", IntT1),
 *         tla.int(1),
 *       ),
 *       tla.neql(
 *         tla.name("x", StrT1),
 *         tla.str("1")
 *       )
 *     )
 * }}}
 * In this case, `x` appears as both `Int` and `Str` typed within the scope of `ex`, which is disallowed. </li>
 *
 * </ul>
 *
 * '''IMPORTANT: EXCEPTIONS WILL ONLY BE THROWN AFTER A `TBuilderInstruction => TlaEx` CONVERSION (IMPLICIT OR
 * EXPLICIT). INVOKING BUILDER METHODS WITHOUT CONVERTING WILL NOT THROW THE ABOVE EXCEPTIONS.'''
 */
package object types {

  import at.forsyte.apalache.tla.typecomp._

  /**
   * A short-hand to the instance of the typed builder, so one can easily construct expressions.
   *
   * You can import all of its methods via:
   *
   * {{{
   * // import implicit conversions
   * import at.forsyte.apalache.tla.types._
   * // import the names from the tla object
   * import at.forsyte.apalache.tla.types.tla._
   * }}}
   *
   * @see
   *   [[types]] for usage instrucitons.
   * @see
   *   [[at.forsyte.apalache.tla.typecomp.ScopedBuilder ScopedBuilder]] for implementation details.
   */
  val tla: ScopedBuilder = new ScopedBuilder(strict = true)
}

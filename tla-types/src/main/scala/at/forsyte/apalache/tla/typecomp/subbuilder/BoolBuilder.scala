package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeBoolBuilder
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.BuilderUtil._

/**
 * Scope-safe builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait BoolBuilder {
  private val unsafeBuilder = new UnsafeBoolBuilder

  /** {{{args[0] /\ ... /\ args[n]}}} */
  def and(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(unsafeBuilder.and(_: _*))

  /** {{{args[0] \/ ... \/ args[n]}}} */
  def or(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(unsafeBuilder.or(_: _*))

  /** {{{~p}}} */
  def not(p: TBuilderInstruction): TBuilderInstruction = p.map(unsafeBuilder.not)

  /** {{{p => q}}} */
  def impl(p: TBuilderInstruction, q: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(p, q)(unsafeBuilder.impl)

  /** {{{p <=> q}}} */
  def equiv(p: TBuilderInstruction, q: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(p, q)(unsafeBuilder.equiv)

  /**
   * {{{\A x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def forall(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(unsafeBuilder.forall)(x, set, p)

  /**
   * {{{\A x: p}}}
   * @param x
   *   must be a variable name
   */
  def forall(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.forall)(x, p)

  /**
   * {{{\E x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def exists(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(unsafeBuilder.exists)(x, set, p)

  /**
   * {{{\E x: p}}}
   * @param x
   *   must be a variable name
   */
  def exists(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.exists)(x, p)

}

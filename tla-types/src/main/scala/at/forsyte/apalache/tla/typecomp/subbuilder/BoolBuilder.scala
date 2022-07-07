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
trait BoolBuilder extends UnsafeBoolBuilder {

  /** args[0] /\ ... /\ args[n] */
  def and(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(_and(_: _*))

  /** args[0] \/ ... \/ args[n] */
  def or(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(_or(_: _*))

  /** ~p */
  def not(p: TBuilderInstruction): TBuilderInstruction = p.map(_not)

  /** p => q */
  def impl(p: TBuilderInstruction, q: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(p, q)(_impl)

  /** p <=> q */
  def equiv(p: TBuilderInstruction, q: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(p, q)(_equiv)

  /** \A x \in set: p */
  def forall(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(_forall)(x, set, p)

  /** \A x: p */
  def forall(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(_forall)(x, p)

  /** \E x \in set: p */
  def exists(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(_exists)(x, set, p)

  /** \E x: p */
  def exists(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(_exists)(x, p)

}

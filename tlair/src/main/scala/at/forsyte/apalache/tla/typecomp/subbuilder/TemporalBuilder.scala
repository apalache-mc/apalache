package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeTemporalBuilder

/**
 * Scope-safe builder for `at.forsyte.apalache.tla.lir.oper.TlaTempOper` expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait TemporalBuilder {
  private val unsafeBuilder = new UnsafeTemporalBuilder {}

  /** {{{[]P}}} */
  def box(P: TBuilderInstruction): TBuilderInstruction = P.map(unsafeBuilder.box)

  /** {{{<>P}}} */
  def diamond(P: TBuilderInstruction): TBuilderInstruction = P.map(unsafeBuilder.diamond)

  /** {{{P ~> Q}}} */
  def leadsTo(P: TBuilderInstruction, Q: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(P, Q)(unsafeBuilder.leadsTo)

  /** {{{P -+-> Q}}} */
  def guarantees(P: TBuilderInstruction, Q: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(P, Q)(unsafeBuilder.guarantees)

  /** {{{WF_x(A)}}} */
  def WF(x: TBuilderInstruction, A: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, A)(unsafeBuilder.WF)

  /** {{{SF_x(A)}}} */
  def SF(x: TBuilderInstruction, A: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, A)(unsafeBuilder.SF)

  /**
   * {{{\EE x: P}}}
   * @param x
   *   must be a variable name
   */
  def EE(x: TBuilderInstruction, P: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.EE)(x, P)

  /**
   * {{{\AA x: P}}}
   * @param x
   *   must be a variable name
   */
  def AA(x: TBuilderInstruction, P: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.AA)(x, P)
}

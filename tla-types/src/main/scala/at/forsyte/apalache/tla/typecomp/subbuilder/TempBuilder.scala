package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeTempBuilder

/**
 * Type-safe builder for TlaTempOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait TempBuilder extends UnsafeTempBuilder {

  /** {{{[]P}}} */
  def box(P: TBuilderInstruction): TBuilderInstruction = P.map(_box)

  /** {{{<>P}}} */
  def diamond(P: TBuilderInstruction): TBuilderInstruction = P.map(_diamond)

  /** {{{P ~> Q}}} */
  def leadsTo(P: TBuilderInstruction, Q: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(P, Q)(_leadsTo)

  /** {{{P -+-> Q}}} */
  def guarantees(P: TBuilderInstruction, Q: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(P, Q)(_guarantees)

  /** {{{WF_x(A)}}} */
  def WF(x: TBuilderInstruction, A: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, A)(_WF)

  /** {{{SF_x(A)}}} */
  def SF(x: TBuilderInstruction, A: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, A)(_SF)

  /** {{{\EE x: P}}} */
  def EE(x: TBuilderInstruction, P: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(_EE)(x, P)

  /** {{{\AA x: P}}} */
  def AA(x: TBuilderInstruction, P: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(_AA)(x, P)
}

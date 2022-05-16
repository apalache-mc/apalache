package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaActionOper

/**
 * Type-unsafe builder for base TlaActionOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeActionBuilder extends ProtoBuilder {

  /** e' */
  protected def _prime(e: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.prime, e)

  /** [A]_e */
  protected def _stutt(A: TlaEx, e: TlaEx): TlaEx =
    buildBySignatureLookup(TlaActionOper.stutter, A, e)

  /** <A>_e */
  protected def _nostutt(A: TlaEx, e: TlaEx): TlaEx =
    buildBySignatureLookup(TlaActionOper.nostutter, A, e)

  /** ENABLED A */
  protected def _enabled(A: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.enabled, A)

  /** UNCHANGED e */
  protected def _unchanged(e: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.unchanged, e)

  /** A \cdot B */
  protected def _comp(A: TlaEx, B: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.composition, A, B)
}

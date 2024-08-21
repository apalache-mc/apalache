package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaActionOper

/**
 * Scope-unsafe builder for base TlaActionOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeActionBuilder extends ProtoBuilder {

  /** {{{e'}}} */
  def prime(e: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.prime, e)

  /** {{{[A]_e}}} */
  def stutt(A: TlaEx, e: TlaEx): TlaEx =
    buildBySignatureLookup(TlaActionOper.stutter, A, e)

  /** {{{<A>_e}}} */
  def nostutt(A: TlaEx, e: TlaEx): TlaEx =
    buildBySignatureLookup(TlaActionOper.nostutter, A, e)

  /** {{{ENABLED A}}} */
  def enabled(A: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.enabled, A)

  /** {{{UNCHANGED e}}} */
  def unchanged(e: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.unchanged, e)

  /** {{{A \cdot B}}} */
  def comp(A: TlaEx, B: TlaEx): TlaEx = buildBySignatureLookup(TlaActionOper.composition, A, B)
}

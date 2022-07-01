package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper

/**
 * Type-unsafe builder for TlaFiniteSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeFiniteSetBuilder extends ProtoBuilder {

  /** IsFiniteSet(set) */
  protected def _isFiniteSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaFiniteSetOper.isFiniteSet, set)

  /** Cardinality(set) */
  protected def _card(set: TlaEx): TlaEx = buildBySignatureLookup(TlaFiniteSetOper.cardinality, set)
}

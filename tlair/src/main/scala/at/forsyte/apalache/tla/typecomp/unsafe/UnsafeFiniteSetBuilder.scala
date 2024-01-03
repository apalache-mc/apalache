package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper

/**
 * Scope-unsafe builder for TlaFiniteSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeFiniteSetBuilder extends ProtoBuilder {

  /** {{{IsFiniteSet(set)}}} */
  def isFiniteSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaFiniteSetOper.isFiniteSet, set)

  /** {{{Cardinality(set)}}} */
  def cardinality(set: TlaEx): TlaEx = buildBySignatureLookup(TlaFiniteSetOper.cardinality, set)
}

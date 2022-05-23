package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
 * Type-unsafe builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeBoolBuilder extends ProtoBuilder {

  /** args[0] /\ ... /\ args[n] */
  protected def _and(args: TlaEx*): TlaEx = buildBySignatureLookup(TlaBoolOper.and, args: _*)

  /** args[0] \/ ... \/ args[n] */
  protected def _or(args: TlaEx*): TlaEx = buildBySignatureLookup(TlaBoolOper.or, args: _*)

  /** ~p */
  protected def _not(p: TlaEx): TlaEx = buildBySignatureLookup(TlaBoolOper.not, p)

  /** p => q */
  protected def _impl(p: TlaEx, q: TlaEx): TlaEx = buildBySignatureLookup(TlaBoolOper.implies, p, q)

  /** p <=> q */
  protected def _equiv(p: TlaEx, q: TlaEx): TlaEx = buildBySignatureLookup(TlaBoolOper.equiv, p, q)

  /** \A x \in set: p */
  protected def _forall(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaBoolOper.forall, x, set, p)
  }

  /** \A x: p */
  protected def _forall(x: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaBoolOper.forallUnbounded, x, p)
  }

  /** \E x \in set: p */
  protected def _exists(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaBoolOper.exists, x, set, p)
  }

  /** \E x: p */
  protected def _exists(x: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaBoolOper.existsUnbounded, x, p)
  }
}

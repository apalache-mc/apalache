package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
 * Raw builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait RawBoolBuilder extends ProtoBuilder {
  // /\_{i=1}^n args
  protected def _and(args: TlaEx*): TlaEx = simpleInstruction(TlaBoolOper.and, args: _*)

  // \/_{i=1}^n args
  protected def _or(args: TlaEx*): TlaEx = simpleInstruction(TlaBoolOper.or, args: _*)

  // ~p
  protected def _not(p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.not, p)

  // p => q
  protected def _impl(p: TlaEx, q: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.implies, p, q)

  // p <=> q
  protected def _equiv(p: TlaEx, q: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.equiv, p, q)

  // \A x \in set: p
  protected def _forall(x: NameEx, set: TlaEx, p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.forall, x, set, p)

  // \A x: p
  protected def _forall(x: NameEx, p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.forallUnbounded, x, p)

  // \E x \in set: p
  protected def _exists(x: NameEx, set: TlaEx, p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.exists, x, set, p)

  // \E x: p
  protected def _exists(x: NameEx, p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.existsUnbounded, x, p)
}

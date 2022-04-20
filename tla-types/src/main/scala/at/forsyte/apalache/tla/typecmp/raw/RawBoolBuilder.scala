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
  protected def _and(args: TlaEx*): TlaEx = simpleInstruction(TlaBoolOper.and, args.size).build(args: _*)

  protected def _or(args: TlaEx*): TlaEx = simpleInstruction(TlaBoolOper.or, args.size).build(args: _*)

  protected def _not(p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.not, 1).build(p)

  protected def _impl(p: TlaEx, q: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.implies, 2).build(p, q)

  protected def _equiv(p: TlaEx, q: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.equiv, 2).build(p, q)

  protected def _forall(elem: NameEx, set: TlaEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.forall, 3).build(elem, set, pred)

  protected def _forall(elem: NameEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.forallUnbounded, 2).build(elem, pred)

  protected def _exists(elem: NameEx, set: TlaEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.exists, 3).build(elem, set, pred)

  protected def _exists(elem: NameEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.existsUnbounded, 2).build(elem, pred)
}

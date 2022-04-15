package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper}

/**
 * Builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait BoolBuilder extends ProtoBuilder {
  def and(args: TlaEx*): TlaEx = simpleInstruction(TlaBoolOper.and, args.size).build(args: _*)

  def or(args: TlaEx*): TlaEx = simpleInstruction(TlaBoolOper.or, args.size).build(args: _*)

  def not(p: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.not, 1).build(p)

  def impl(p: TlaEx, q: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.implies, 2).build(p, q)

  def equiv(p: TlaEx, q: TlaEx): TlaEx = simpleInstruction(TlaBoolOper.equiv, 2).build(p, q)

  def forall(elem: TlaEx, set: TlaEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.forall, 3).build(elem, set, pred)

  def forall(elem: TlaEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.forallUnbounded, 2).build(elem, pred)

  def exists(elem: TlaEx, set: TlaEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.exists, 3).build(elem, set, pred)

  def exists(elem: TlaEx, pred: TlaEx): TlaEx =
    simpleInstruction(TlaBoolOper.existsUnbounded, 2).build(elem, pred)

}

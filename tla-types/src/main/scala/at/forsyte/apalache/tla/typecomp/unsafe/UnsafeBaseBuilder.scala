package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
 * Type-unsafe builder for base TlaOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeBaseBuilder extends ProtoBuilder {

  /** lhs = rhs */
  protected def _eql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.eq, lhs, rhs)

  /** lhs /= rhs */
  protected def _neql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.ne, lhs, rhs)

  /** Op(args[1],...,args[n]) */
  protected def _appOp(Op: TlaEx, args: TlaEx*): TlaEx = buildBySignatureLookup(TlaOper.apply, Op +: args: _*)

  /** CHOOSE x: p */
  protected def _choose(x: TlaEx, p: TlaEx): TlaEx =
    buildBySignatureLookup(TlaOper.chooseUnbounded, x, p)

  /** CHOOSE x \in set: p */
  protected def _choose(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx =
    buildBySignatureLookup(TlaOper.chooseBounded, x, set, p)

  /** args[0](args[1], ..., args[n]) :: ex */
  protected def _label(ex: TlaEx, args: String*): TlaEx = {
    require(args.nonEmpty)
    val argsAsStringExs = args.map { s => ValEx(TlaStr(s))(Typed(StrT1)) }
    buildBySignatureLookup(TlaOper.label, ex +: argsAsStringExs: _*)
  }
}

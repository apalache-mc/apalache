package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
 * Scope-unsafe builder for base TlaOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeBaseBuilder extends ProtoBuilder {

  /** {{{lhs = rhs}}} */
  def eql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.eq, lhs, rhs)

  /** {{{lhs /= rhs}}} */
  def neql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.ne, lhs, rhs)

  /** {{{Op(args[1],...,args[n])}}} */
  def appOp(Op: TlaEx, args: TlaEx*): TlaEx = buildBySignatureLookup(TlaOper.apply, Op +: args: _*)

  /** {{{CHOOSE x: p}}} `x` must be a variable name */
  def choose(x: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaOper.chooseUnbounded, x, p)
  }

  /** {{{CHOOSE x \in set: p}}}, `x` must be a variable name */
  def choose(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaOper.chooseBounded, x, set, p)
  }

  /** {{{args[0](args[1], ..., args[n]) :: ex}}} `args` must be nonempty */
  def label(ex: TlaEx, args: String*): TlaEx = {
    require(args.nonEmpty)
    val argsAsStringExs = args.map { s => ValEx(TlaStr(s))(Typed(StrT1)) }
    buildBySignatureLookup(TlaOper.label, ex +: argsAsStringExs: _*)
  }
}

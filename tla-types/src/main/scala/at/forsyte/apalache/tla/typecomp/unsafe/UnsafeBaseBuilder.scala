package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper

/**
 * Scope-unsafe builder for base TlaOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeBaseBuilder extends ProtoBuilder {

  // We borrow the LiteralBuilder to make TLA strings from Scala strings
  private val strBuilder = new UnsafeLiteralAndNameBuilder
  private def mkTlaStr: String => TlaEx = strBuilder.str

  /** {{{lhs = rhs}}} */
  def eql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.eq, lhs, rhs)

  /** {{{lhs /= rhs}}} */
  def neql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.ne, lhs, rhs)

  /** {{{Op(args[1],...,args[n])}}} */
  def appOp(Op: TlaEx, args: TlaEx*): TlaEx = buildBySignatureLookup(TlaOper.apply, Op +: args: _*)

  /**
   * {{{CHOOSE x: p}}}
   * @param x
   *   must be a variable name
   */
  def choose(x: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx], s"Expected x to be a variable name, found $x.")
    buildBySignatureLookup(TlaOper.chooseUnbounded, x, p)
  }

  /**
   * {{{CHOOSE x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def choose(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx], s"Expected x to be a variable name, found $x.")
    buildBySignatureLookup(TlaOper.chooseBounded, x, set, p)
  }

  /**
   * {{{args[0](args[1], ..., args[n]) :: ex}}}
   * @param args
   *   must be nonempty
   */
  def label(ex: TlaEx, args: String*): TlaEx = {
    require(args.nonEmpty, s"args must be nonempty.")
    val argsAsStringExs = args.map { mkTlaStr }
    buildBySignatureLookup(TlaOper.label, ex +: argsAsStringExs: _*)
  }
}

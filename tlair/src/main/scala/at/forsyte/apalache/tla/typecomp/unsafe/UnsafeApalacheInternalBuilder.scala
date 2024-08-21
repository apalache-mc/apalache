package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, TlaOper}

/**
 * Scope-unsafe builder for ApalacheInternalOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeApalacheInternalBuilder extends ProtoBuilder with UnsafeLiteralAndNameBuilder {
  // We extend LiteralBuilder to make TLA strings from Scala strings

  /**
   * {{{__NotSupportedByModelChecker(msg): t}}}
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   */
  def notSupportedByModelChecker(msg: String, tt: TlaType1): TlaEx =
    OperEx(ApalacheInternalOper.notSupportedByModelChecker, str(msg))(Typed(tt))

  /**
   * distinct
   */
  def distinct(args: TlaEx*): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.distinct, args: _*)

  /** {{{__ApalacheSeqCapacity(seq)}}} */
  def apalacheSeqCapacity(seq: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.apalacheSeqCapacity, seq)

  /** selectInSet */
  def selectInSet(elem: TlaEx, set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.selectInSet, elem, set)

  /** selectInFun */
  def selectInFun(elem: TlaEx, fun: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.selectInFun, elem, fun)

  /** storeNotInSet */
  def storeNotInSet(elem: TlaEx, set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeNotInSet, elem, set)

  /** storeNotInFun */
  def storeNotInFun(elem: TlaEx, fun: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeNotInFun, elem, fun)

  /** storeInSet */
  def storeInSet(elem: TlaEx, set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeInSet, elem, set)

  /** storeInSet */
  def storeInSet(elem: TlaEx, fun: TlaEx, arg: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeInSet, elem, fun, arg)

  /** smtMap */
  def smtMap(oper: TlaOper, set1: TlaEx, set2: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.smtMap(oper), set1, set2)

  /** unconstrainArray */
  def unconstrainArray(set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.unconstrainArray, set)
}

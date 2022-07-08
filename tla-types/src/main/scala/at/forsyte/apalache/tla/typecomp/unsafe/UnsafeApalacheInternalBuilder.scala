package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
 * Scope-unsafe builder for ApalacheInternalOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeApalacheInternalBuilder extends ProtoBuilder {

  /**
   * notSupportedByModelChecker
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   */
  protected def _notSupportedByModelChecker(msg: String, tt: TlaType1): TlaEx =
    OperEx(ApalacheInternalOper.notSupportedByModelChecker, ValEx(TlaStr(msg))(Typed(StrT1)))(Typed(tt))

  /** distinct */
  protected def _distinct(args: TlaEx*): TlaEx = {
    require(args.nonEmpty)
    buildBySignatureLookup(ApalacheInternalOper.distinct, args: _*)
  }

  /** apalacheSeqCapacity */
  protected def _apalacheSeqCapacity(seq: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.apalacheSeqCapacity, seq)

  /** selectInSet */
  protected def _selectInSet(elem: TlaEx, set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.selectInSet, elem, set)

  /** storeNotInSet */
  protected def _storeNotInSet(elem: TlaEx, set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeNotInSet, elem, set)

  /** storeInSet */
  protected def _storeInSet(elem: TlaEx, set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeInSet, elem, set)

  /** storeInSet */
  protected def _storeInSet(elem: TlaEx, fun: TlaEx, arg: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.storeInSet, elem, fun, arg)

  /** smtMap */
  protected def _smtMap(oper: TlaOper, set1: TlaEx, set2: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.smtMap(oper), set1, set2)

  /** unconstrainArray */
  protected def _unconstrainArray(set: TlaEx): TlaEx =
    buildBySignatureLookup(ApalacheInternalOper.unconstrainArray, set)
}

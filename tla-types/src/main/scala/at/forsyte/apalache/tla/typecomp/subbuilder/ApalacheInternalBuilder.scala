package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeApalacheInternalBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Type-safe builder for ApalacheInternalOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ApalacheInternalBuilder extends UnsafeApalacheInternalBuilder {

  /** notSupportedByModelChecker */
  def notSupportedByModelChecker(msg: String, tt: TlaType1): TBuilderInstruction =
    _notSupportedByModelChecker(msg, tt).point[TBuilderInternalState]

  /** distinct */
  def distinct(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map(_distinct(_: _*))

  /** apalacheSeqCapacity */
  def apalacheSeqCapacity(seq: TBuilderInstruction): TBuilderInstruction = seq.map(_apalacheSeqCapacity)

  /** selectInSet */
  def selectInSet(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_selectInSet)

  /** storeNotInSet */
  def storeNotInSet(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_storeNotInSet)

  /** storeInSet */
  def storeInSet(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_storeInSet)

  /** storeInSet */
  def storeInSet(elem: TBuilderInstruction, fun: TBuilderInstruction, arg: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(elem, fun, arg)(_storeInSet)

  /** smtMap */
  def smtMap(oper: TlaOper, set1: TBuilderInstruction, set2: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(set1, set2)(_smtMap(oper, _, _))

  /** unconstrainArray */
  def unconstrainArray(set: TBuilderInstruction): TBuilderInstruction =
    set.map(_unconstrainArray)
}

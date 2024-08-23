package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeApalacheInternalBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Scope-safe builder for ApalacheInternalOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ApalacheInternalBuilder {
  private val unsafeBuilder = new UnsafeApalacheInternalBuilder {}

  /**
   * {{{__NotSupportedByModelChecker(msg): t}}}
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   */
  def notSupportedByModelChecker(msg: String, tt: TlaType1): TBuilderInstruction =
    unsafeBuilder.notSupportedByModelChecker(msg, tt).point[TBuilderInternalState]

  /**
   * distinct
   * @param args
   *   must be nonempty
   */
  def distinct(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map(unsafeBuilder.distinct(_: _*))

  /** {{{__ApalacheSeqCapacity(seq)}}} */
  def apalacheSeqCapacity(seq: TBuilderInstruction): TBuilderInstruction = seq.map(unsafeBuilder.apalacheSeqCapacity)

  /** selectInSet */
  def selectInSet(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(unsafeBuilder.selectInSet)

  /** selectInFun */
  def selectInFun(elem: TBuilderInstruction, fun: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, fun)(unsafeBuilder.selectInFun)

  /** storeNotInSet */
  def storeNotInSet(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(unsafeBuilder.storeNotInSet)

  /** storeNotInFun */
  def storeNotInFun(elem: TBuilderInstruction, fun: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, fun)(unsafeBuilder.storeNotInFun)

  /** storeInSet binary (sets) */
  def storeInSet(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(unsafeBuilder.storeInSet)

  /** storeInSet ternary (functions) */
  def storeInSet(elem: TBuilderInstruction, fun: TBuilderInstruction, arg: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(elem, fun, arg)(unsafeBuilder.storeInSet)

  /** smtMap */
  def smtMap(oper: TlaOper, set1: TBuilderInstruction, set2: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(set1, set2)(unsafeBuilder.smtMap(oper, _, _))

  /** unconstrainArray */
  def unconstrainArray(set: TBuilderInstruction): TBuilderInstruction =
    set.map(unsafeBuilder.unconstrainArray)
}

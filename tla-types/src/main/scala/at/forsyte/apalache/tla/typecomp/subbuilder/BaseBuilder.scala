package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.BuilderUtil.{binaryFromUnsafe, buildSeq, ternaryFromUnsafe}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeBaseBuilder

/**
 * Type-safe builder for base TlaOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait BaseBuilder extends UnsafeBaseBuilder {

  /** lhs = rhs */
  def eql(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(_eql)

  /** lhs /= rhs */
  def neql(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(_neql)

  /** Op(args[1],...,args[n]) */
  def appOp(Op: TBuilderInstruction, args: TBuilderInstruction*): TBuilderInstruction = for {
    opEx <- Op
    argsExs <- buildSeq(args)
  } yield _appOp(opEx, argsExs: _*)

  /** CHOOSE x: p */
  def choose(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, p)(_choose)

  /** CHOOSE x \in set: p */
  def choose(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(x, set, p)(_choose)

  /** args[0](args[1], ..., args[n]) :: ex */
  def label(ex: TBuilderInstruction, args: String*): TBuilderInstruction =
    ex.map { e => _label(e, args: _*) }
}

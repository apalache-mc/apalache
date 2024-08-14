package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeBaseBuilder

/**
 * Scope-safe builder for base TlaOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait BaseBuilder {
  private val unsafeBuilder = new UnsafeBaseBuilder {}

  /** {{{lhs = rhs}}} */
  def eql(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(unsafeBuilder.eql)

  /** {{{lhs /= rhs}}} */
  def neql(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(unsafeBuilder.neql)

  /** {{{Op(args[1],...,args[n])}}} */
  def appOp(Op: TBuilderInstruction, args: TBuilderInstruction*): TBuilderInstruction = for {
    opEx <- Op
    argsExs <- buildSeq(args)
  } yield unsafeBuilder.appOp(opEx, argsExs: _*)

  /**
   * {{{CHOOSE x: p}}}
   * @param x
   *   must be a variable name
   */
  def choose(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.choose)(x, p)

  /**
   * {{{CHOOSE x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def choose(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(unsafeBuilder.choose)(x, set, p)

  /**
   * {{{args[0](args[1], ..., args[n]) :: ex}}}
   * @param args
   *   must be nonempty
   */
  def label(ex: TBuilderInstruction, args: String*): TBuilderInstruction =
    ex.map { e => unsafeBuilder.label(e, args: _*) }
}

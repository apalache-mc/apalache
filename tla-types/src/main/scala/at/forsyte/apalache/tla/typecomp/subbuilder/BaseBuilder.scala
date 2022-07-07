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
trait BaseBuilder extends UnsafeBaseBuilder {

  /** {{{lhs = rhs}}} */
  def eql(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(_eql)

  /** {{{lhs /= rhs}}} */
  def neql(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(_neql)

  /** {{{Op(args[1],...,args[n])}}} */
  def appOp(Op: TBuilderInstruction, args: TBuilderInstruction*): TBuilderInstruction = for {
    opEx <- Op
    argsExs <- buildSeq(args)
  } yield _appOp(opEx, argsExs: _*)

  /** {{{CHOOSE x: p}}} `x` must be a variable name */
  def choose(x: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(_choose)(x, p)

  /** {{{CHOOSE x \in set: p}}}, `x` must be a variable name */
  def choose(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(_choose)(x, set, p)

  /** {{{args[0](args[1], ..., args[n]) :: ex}}} `args` must be nonempty */
  def label(ex: TBuilderInstruction, args: String*): TBuilderInstruction =
    ex.map { e => _label(e, args: _*) }
}

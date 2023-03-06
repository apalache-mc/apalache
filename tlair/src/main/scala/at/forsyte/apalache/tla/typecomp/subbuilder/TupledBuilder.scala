package at.forsyte.apalache.tla.typecomp.subbuilder
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeTupledBuilder

/**
 * Scope-safe builder for syntax-sugar.
 *
 * @author
 *   Jure Kukovec
 */
trait TupledBuilder {
  private val unsafeBuilder = new UnsafeTupledBuilder

  /**
   * {{{\A vars \in set: p}}}
   *
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def forallAllowTuples(
      vars: TBuilderInstruction,
      set: TBuilderInstruction,
      p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(unsafeBuilder.forallAllowTuples)(vars, set, p)

  /**
   * {{{\A vars: p}}}
   *
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def forallAllowTuples(vars: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.forallAllowTuples)(vars, p)

  /**
   * {{{\E vars \in set: p}}}
   *
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def existsAllowTuples(
      vars: TBuilderInstruction,
      set: TBuilderInstruction,
      p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(unsafeBuilder.existsAllowTuples)(vars, set, p)

  /**
   * {{{\E vars: p}}}
   *
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def existsAllowTuples(vars: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionBinary(unsafeBuilder.existsAllowTuples)(vars, p)
}

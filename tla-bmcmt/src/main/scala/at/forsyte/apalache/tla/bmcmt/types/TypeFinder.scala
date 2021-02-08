package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, TypeException}
import at.forsyte.apalache.tla.lir.TlaEx

import scala.collection.immutable.{Map, SortedMap}

/**
 * A diagnostic message that is added in a list of errors.
 *
 * @param origin      the expression that caused the type error
 * @param explanation the explanation
 */
class TypeInferenceError(val origin: TlaEx, val explanation: String)

/**
 * A general interface to a type inference engine. Check the description in docs/types-api.md.
 *
 * @tparam T the base class of the type system
 * @see CellT
 * @author Igor Konnov
 */
trait TypeFinder[T] {

  /**
   * Given a TLA+ expression, reconstruct the types and store them in an internal storage.
   * If the expression is not well-typed, this method will not throw TypeInferenceError,
   * but will collect a list of error that can be access with getTypeErrors.
   *
   * @param e a TLA+ expression.
   * @return Some(type), if successful, and None otherwise
   */
  def inferAndSave(e: TlaEx): Option[T]

  /**
   * Retrieve the type errors from the latest call to inferAndSave.
   *
   * @return a list of type errors
   */
  def typeErrors: Seq[TypeInferenceError]

  /**
   * Given a TLA+ expression and the types of its arguments, compute the resulting type, if possible.
   * This function uses the types that were pre-computed by inferAndSave. It should also work for arbitrary
   * expressions, as soon as they can be unambiguously typed with the previously stored type information
   * and the given arguments.
   *
   * @param e        a TLA+ expression
   * @param argTypes the types of the arguments.
   * @return the resulting type, if it can be computed
   * @throws TypeException , if the type cannot be computed.
   */
  def compute(e: TlaEx, argTypes: T*): T

  /**
   * Call compute recursively to compute the type of a given expression. This function is expensive,
   * use it only when absolutely necessary. If the expression is referring to variables, inferAndSave should have
   * been called before.
   *
   * @param ex a TLA+ expression
   * @return the resulting type
   */
  def computeRec(ex: TlaEx): CellT

  /**
   * Get the types of the variables that are computed by inferAndSave. The method must return the types of
   * the global variables (VARIABLE and CONSTANT) and it may return types of the bound variables.
   *
   * @return a mapping of names to types
   */
  def varTypes: SortedMap[String, T]

  /**
   * Restore variable types from a map. This method does not update type annotations.
   *
   * @param newVarTypes a mapping of names to types
   */
  def varTypes_(newVarTypes: SortedMap[String, CellT]): Unit

  /**
   * Record the cell name and its type.
   *
   * @param cell an arena cell
   */
  def extendWithCellType(cell: ArenaCell): Unit

  /**
   * Forget all computed types and introduce types for the variables. You can call inferAndSave after that.
   *
   * @param varTypes types of the global variables (VARIABLE and CONSTANT)
   */
  def reset(varTypes: Map[String, T]): Unit
}

package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}

/**
 * <p>An abstract writer of TLA+ expressions. For an example, see `PrettyWriter`.</p>
 *
 * <p>Igor: We should refactor the writers' architecture. Use the Writer monad?</p>
 */
trait TlaWriter {

  /**
   * Write a module, including all declarations
   *
   * @param mod                 a module
   * @param extendedModuleNames the names of the modules to be extended
   */
  def write(mod: TlaModule, extendedModuleNames: List[String]): Unit

  /**
   * Write a declaration, including all expressions
   *
   * @param decl a declaration
   */
  def write(decl: TlaDecl): Unit

  /**
   * Write a TLA+ expression.
   *
   * @param expr an expression
   */
  def write(expr: TlaEx): Unit
}

object TlaWriter {

  /**
   * The names of all standard modules that are supported by Apalache IR.
   */
  val STANDARD_MODULES = List("Integers", "Sequences", "FiniteSets", "TLC", "Apalache")

}

package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}

import java.io.{File, FileWriter, PrintWriter}

/**
 * <p>An abstract writer of TLA+ expressions. For an example, see `PrettyWriter`.</p>
 *
 * <p>Igor: We should refactor the writers' architecture. Use the Writer monad?</p>
 */
trait TlaWriter {

  /**
   * Write a module, including all declarations
   *
   * @param mod a module
   */
  def write(mod: TlaModule): Unit

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

package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.io.ConfigurationError

/**
 * Interface for the subcommands that run an `Executor`
 *
 * @author
 *   Shon Feder
 */
abstract class PassExecutorCmd(name: String, description: String)
    extends ApalacheCommand(name: String, description: String) {

  /**
   * The executor used to sequence a chain of passes
   *
   * Executors are created using `at.forsyte.apalache.infra.passes.ToolModule`. E.g.,
   *
   * {{{
   * val executor = Executor(new TypeCheckerModule)
   * }}}
   *
   * The [[run]] methods of a subcommand implementing this trait will generally end with an invication of
   * `executor.run`, such as
   *
   * {{{
   * executor.run() match {
   *   case Right(module) => Right("Success msg")
   *   case Left(errCode) => Left(errorCode, "Failure msg")
   * }
   * }}}
   */
  val executor: Executor

  /**
   * Sets the common options in the [[executor]]
   *
   * This may be overridden by classes to change which options the class considers common.
   *
   * NOTE: It is not invoked automatically, and you should invoke it explicitly in your `Cmd` class' [[run]] method.
   */
  def setCommonOptions(): Unit = {
    // TODO: rm after options provider wired in
    val cfg = configuration.left.map(err => new ConfigurationError(err)).toTry.get
    executor.passOptions
      .set("general.debug", cfg.common.debug.get)
    executor.passOptions.set("smt.prof", cfg.common.smtprof.get)
    executor.passOptions.set("general.features", cfg.common.features.get)
  }
}

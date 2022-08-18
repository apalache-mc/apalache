package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.infra.passes.options.OptionGroup

/**
 * Interface for the subcommands that run an `Executor`
 *
 * @author
 *   Shon Feder
 */
abstract class PassExecutorCmd(name: String, description: String)
    extends ApalacheCommand(name: String, description: String) {

  // TODO: we should be able to remove this type once `PassOptions` is replaced by the options provider
  type Options <: OptionGroup.HasCommon

  /**
   * Sets the common options in the supplied [[infra.Executor Executor]]
   *
   * This may be overridden by classes to change which options the class considers common.
   *
   * NOTE: It is not invoked automatically, and you should invoke it explicitly in your `Cmd` class' [[run]] method.
   */
  // TODO: rm once options provider is fully integrated
  def setCommonOptions(executor: Executor[Options]): Unit = {
    val options = executor.options.common
    executor.passOptions.set("general.debug", options.debug)
    executor.passOptions.set("smt.prof", options.smtprof)
    executor.passOptions.set("general.features", options.features)
  }
}

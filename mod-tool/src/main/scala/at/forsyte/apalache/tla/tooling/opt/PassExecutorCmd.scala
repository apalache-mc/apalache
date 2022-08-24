package at.forsyte.apalache.tla.tooling.opt

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
}

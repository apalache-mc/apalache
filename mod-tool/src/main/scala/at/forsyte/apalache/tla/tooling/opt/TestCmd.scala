package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist._

import java.io.File
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.Algorithm

/**
 * This command initiates the 'test' command line.
 *
 * @author
 *   Igor Konnov
 */
class TestCmd
    extends ApalacheCommand(name = "test", description = "Quickly test a TLA+ specification") with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var before: String =
    arg[String](name = "before", description = "the name of an operator to prepare the test, similar to Init")
  var action: String =
    arg[String](name = "action", description = "the name of an action to execute, similar to Next")
  var assertion: String =
    arg[String](name = "assertion",
        description = "the name of an operator that should evaluate to true after executing `action`")
  var cinit: Option[String] = opt[Option[String]](name = "cinit", default = None,
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")

  override def toConfig() = for {
    cfg <- super.toConfig()
    input <- SourceOption.FileSource(file).map(src => cfg.input.copy(source = Some(src)))

    // Tune for testing:
    //   1. Check the invariant only after the action took place.
    //   2. Randomize
    seed = Math.abs(System.currentTimeMillis().toInt)
  } yield cfg.copy(
      input = input,
      checker = cfg.checker.copy(
          tuning = Some(Map("search.invariantFilter" -> "1->.*", "smt.randomSeed" -> seed.toString)),
          init = Some(before),
          next = Some(action),
          inv = Some(List(assertion)),
          cinit = cinit,
          nworkers = Some(1),
          length = Some(1),
          discardDisabled = Some(false),
          noDeadlocks = Some(false),
          algo = Some(Algorithm.Offline),
      ),
      typechecker = cfg.typechecker.copy(
          inferpoly = Some(true)
      ),
  )

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithCheckerPreds(cfg).get

    // This is a special version of the `check` command that is tuned towards testing scenarios
    logger.info("Checker passOptions: filename=%s, before=%s, action=%s, after=%s"
          .format(file, before, action, assertion))

    val tuning = options.checker.tuning
    // val tuning = Map("search.invariantFilter" -> "1->.*", "smt.randomSeed" -> seed.toString)
    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    PassChainExecutor.run(new CheckerModule(options)) match {
      case Right(_)      => Right("No example found")
      case Left(failure) => Left(failure.exitCode, "Found a violation of the postcondition. Check violation.tla.")
    }

  }
}

package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist._

import java.io.File
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.io.ConfigurationError

/**
 * This command initiates the 'test' command line.
 *
 * @author
 *   Igor Konnov
 */
class TestCmd
    extends PassExecutorCmd(name = "test", description = "Quickly test a TLA+ specification") with LazyLogging {

  val executor = Executor(new CheckerModule)

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

  override def toConfig(): Config.ApalacheConfig = {
    val cfg = super.toConfig()

    // Tune for testing:
    //   1. Check the invariant only after the action took place.
    //   2. Randomize
    val seed = Math.abs(System.currentTimeMillis().toInt)

    cfg.copy(
        common = cfg.common.copy(
            inputfile = Some(file)
        ),
        checker = cfg.checker.copy(
            tuning = Some(Map("search.invariantFilter" -> "1->.*", "smt.randomSeed" -> seed.toString)),
            init = Some(before),
            next = Some(action),
            inv = Some(assertion),
            cinit = cinit,
            nworkers = Some(1),
            length = Some(1),
            discardDisabled = Some(false),
            noDeadlocks = Some(false),
            algo = Some("offline"),
        ),
        typechecker = cfg.typechecker.copy(
            inferpoly = Some(true)
        ),
    )
  }

  def run() = {
    // TODO: rm once OptionProvider is wired in
    val cfg = configuration.left.map(err => new ConfigurationError(err)).toTry.get

    // This is a special version of the `check` command that is tuned towards testing scenarios
    logger.info("Checker passOptions: filename=%s, before=%s, action=%s, after=%s"
          .format(file, before, action, assertion))

    val tuning = cfg.checker.tuning.get
    // val tuning = Map("search.invariantFilter" -> "1->.*", "smt.randomSeed" -> seed.toString)
    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    executor.passOptions.set("general.tuning", tuning)
    executor.passOptions.set("parser.source", SourceOption.FileSource(cfg.common.inputfile.get.getAbsoluteFile))
    executor.passOptions.set("checker.init", cfg.checker.init.get)
    executor.passOptions.set("checker.next", cfg.checker.next.get)
    executor.passOptions.set("checker.inv", List(cfg.checker.inv.get))
    cfg.checker.cinit.foreach(executor.passOptions.set("checker.cinit", _))
    // TODO: move into options provider
    executor.passOptions.set("checker.nworkers", cfg.checker.nworkers.get)
    // check only one instance of the action
    executor.passOptions.set("checker.length", cfg.checker.length.get)
    // no preliminary pruning of disabled transitions
    executor.passOptions.set("checker.discardDisabled", cfg.checker.discardDisabled.get)
    executor.passOptions.set("checker.noDeadlocks", cfg.checker.noDeadlocks.get)
    // prefer the offline mode as we have a single query
    executor.passOptions.set("checker.algo", cfg.checker.algo.get)
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    executor.passOptions.set("typechecker.inferPoly", cfg.typechecker.inferpoly.get)
    setCommonOptions()

    executor.run() match {
      case Right(_)   => Right("No example found")
      case Left(code) => Left(code, "Found a violation of the postcondition. Check violation.tla.")
    }

  }
}

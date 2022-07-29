package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist._

import java.io.File
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.SourceOption

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
  var cinit: String = opt[String](name = "cinit", default = "",
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")

  def run() = {
    // This is a special version of the `check` command that is tuned towards testing scenarios
    logger.info("Checker passOptions: filename=%s, before=%s, action=%s, after=%s"
          .format(file, before, action, assertion))

    // Tune for testing:
    //   1. Check the invariant only after the action took place.
    //   2. Randomize
    val seed = Math.abs(System.currentTimeMillis().toInt)
    val tuning = Map("search.invariantFilter" -> "1", "smt.randomSeed" -> seed.toString)
    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    executor.passOptions.set("general.tuning", tuning)
    executor.passOptions.set("parser.source", SourceOption.FileSource(file.getAbsoluteFile))
    executor.passOptions.set("checker.init", before)
    executor.passOptions.set("checker.next", action)
    executor.passOptions.set("checker.inv", List(assertion))
    if (cinit != "") {
      executor.passOptions.set("checker.cinit", cinit)
    }
    executor.passOptions.set("checker.nworkers", 1)
    // check only one instance of the action
    executor.passOptions.set("checker.length", 1)
    // no preliminary pruning of disabled transitions
    executor.passOptions.set("checker.discardDisabled", false)
    executor.passOptions.set("checker.noDeadlocks", false)
    // prefer the offline mode as we have a single query
    executor.passOptions.set("checker.algo", "offline")
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    executor.passOptions.set("typechecker.inferPoly", true)
    setCommonOptions()

    executor.run() match {
      case Right(_)   => Right("No example found")
      case Left(code) => Left(code, "Found a violation of the postcondition. Check violation.tla.")
    }

  }
}

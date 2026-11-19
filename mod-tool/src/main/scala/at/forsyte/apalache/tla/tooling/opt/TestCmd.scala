package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.config.Constants._
import at.forsyte.apalache.io.config._
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import com.typesafe.scalalogging.LazyLogging
import org.backuity.clist._

import java.io.File

/**
 * This command initiates the 'test' command line.
 *
 * @author
 *   Igor Konnov
 */
class TestCmd extends ApalacheCommand(name = TEST, description = "Quickly test a TLA+ specification") with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var before: String =
    arg[String](name = BEFORE, description = "the name of an operator to prepare the test, similar to Init")
  var action: String =
    arg[String](name = ACTION, description = "the name of an action to execute, similar to Next")
  var assertion: String =
    arg[String](name = ASSERTION,
        description = "the name of an operator that should evaluate to true after executing `action`")
  var cinit: Option[String] = opt[Option[String]](name = CINIT, default = None,
      description = descriptionWithDefault(
          "the name of an operator that initializes CONSTANTS",
          configDefaults.checker.constantInitializer,
      ))

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val base = super.toConfig
    if (!base.isSuccess) return ConfigParseResult.failureFrom(base)
    val source = InputSource.FileSource(file)
    if (!source.isSuccess) return ConfigParseResult.failureFrom(source)

    // Tune for testing:
    //   1. Check the invariant only after the action took place.
    //   2. Randomize
    val seed = System.currentTimeMillis().toInt & Int.MaxValue
    mergeConfig(
        base,
        ApalacheConfig(
            source = Some(source.requireValue()),
            checker = CheckerPatch(
                tuning = Some(Map("search.invariantFilter" -> "1->.*")),
                searchKind = Some(SearchKind.Check),
                seed = Some(seed),
                init = Some(before),
                next = Some(action),
                invariants = Some(List(assertion)),
                constantInitializer = cinit,
                length = Some(1),
                discardDisabled = Some(false),
                checkDeadlocks = Some(true),
                algorithm = Some(Algorithm.Offline),
            ),
        ),
    )
  }

  override def run(config: ApalacheConfig) = {
    runWithOptions(ApalacheConfigResolver.resolveCheck(config)) { options =>
      // This is a special version of the `check` command that is tuned towards testing scenarios
      logger.info("Checker passOptions: filename=%s, before=%s, action=%s, after=%s"
            .format(file, before, action, assertion))

      val tuning = options.checker.tuning
      logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

      PassChainExecutor(new CheckerModule(options)).run() match {
        case Right(_)      => Right("No example found")
        case Left(failure) =>
          Left(failure.exitCode, "Found a violation of the postcondition. Check violation.tla.")
      }
    }
  }
}

package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.PassOptionException
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.config.Constants._
import at.forsyte.apalache.io.config._
import at.forsyte.apalache.io.tuning.FineTuningParser
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import org.apache.commons.configuration2.builder.fluent.Configurations
import org.apache.commons.configuration2.ex.ConfigurationException
import org.apache.commons.io.FilenameUtils
import org.backuity.clist._
import org.backuity.clist.util.Read

import java.io.{File, FileNotFoundException}
import scala.jdk.CollectionConverters._

/**
 * This command initiates the 'check' command line.
 *
 * @author
 *   Igor Konnov
 */
class CheckCmd(name: String = CHECK, description: String = "Check a TLA+ specification")
    extends AbstractCheckerCmd(name, description) {

  private val algorithmDescriptions = List(
      Algorithm.Incremental.name,
      Algorithm.Offline.name,
      s"${Algorithm.Remote.name} (used by explorer)",
  ).mkString(", ")

  private val smtEncodingDescriptions = List(
      SMTEncoding.OOPSLA19.name,
      s"${SMTEncoding.Arrays.name} (experimental)",
      s"${SMTEncoding.FunArrays.name} (experimental)",
  ).mkString(", ")

  private val smtSolverDescriptions = List(
      SMTSolver.Z3.name,
      s"${SMTSolver.CVC5.name} (experimental)",
  ).mkString(", ")

  // Parses the smtEncoding option
  implicit val smtEncodingRead: Read[SMTEncoding] =
    Read.reads[SMTEncoding](s"an SMT encoding: ${SMTEncoding.values.mkString(", ")}")(SMTEncoding.fromString)

  // Parses the smtSolver option
  implicit val smtSolverRead: Read[SMTSolver] =
    Read.reads[SMTSolver](s"an SMT solver backend: ${SMTSolver.values.mkString(", ")}")(SMTSolver.fromString)

  // Parses the algo option
  implicit val algoRead: Read[Algorithm] =
    Read.reads[Algorithm](s"a checking algorithm: ${Algorithm.values.mkString(", ")}")(Algorithm.fromString)

  var algo: Option[Algorithm] = opt[Option[Algorithm]](name = ALGO, default = None,
      description = descriptionWithDefault(
          s"the search algorithm: $algorithmDescriptions",
          configDefaults.checker.algorithm,
      ))
  var smtEncoding: Option[SMTEncoding] = opt[Option[SMTEncoding]](name = SMT_ENCODING, useEnv = true, default = None,
      description = descriptionWithDefault(
          s"the SMT encoding: $smtEncodingDescriptions",
          configDefaults.checker.smtEncoding,
      ) + " (overrides envvar SMT_ENCODING)")
  var smtSolver: Option[SMTSolver] = opt[Option[SMTSolver]](name = SMT_SOLVER, useEnv = true, default = None,
      description = descriptionWithDefault(
          s"the SMT solver backend: $smtSolverDescriptions",
          configDefaults.checker.smtSolver,
      ) + " (overrides envvar SMT_SOLVER)")
  var seed: Option[Int] =
    opt[Option[Int]](name = SEED,
        description = descriptionWithDefault(
            "set a nonnegative random seed for reproducible SMT solving and, with simulate, transition selection",
          "generated per run",
        ), default = None)
  var tuningOptionsFile: Option[String] =
    opt[Option[String]](name = TUNING_OPTIONS_FILE, default = None,
        description = descriptionWithDefault(
            "filename of the tuning options, see docs/tuning.md",
            configDefaults.checker.tuning,
        ))
  var tuningOptions: Option[String] =
    opt[Option[String]](name = TUNING_OPTIONS, default = None,
        description = descriptionWithDefault(
            s"tuning options as arguments in the format key1=val1:key2=val2:key3=val3 " +
              s"(priority over --$TUNING_OPTIONS_FILE)",
            configDefaults.checker.tuning,
        ))
  var discardDisabled: Option[Boolean] = opt[Option[Boolean]](name = DISCARD_DISABLED, default = None,
      description = descriptionWithDefault(
          "pre-check, whether a transition is disabled, and discard it, to make SMT queries smaller",
          configDefaults.checker.discardDisabled,
      ))
  var noDeadlocks: Option[Boolean] =
    opt[Option[Boolean]](name = NO_DEADLOCK, default = None,
        description = descriptionWithDefault(
            "do not check for deadlocks",
            !ApalacheConfigResolver.defaultCheckDeadlocks,
        ))

  var maxError: Option[Int] =
    opt[Option[Int]](name = MAX_ERROR,
        description = descriptionWithDefault(
            s"do not stop on first error, but produce at most the given number of errors " +
              s"(requires --$VIEW when greater than 1)",
            configDefaults.checker.maxError,
        ), default = None)

  var view: Option[String] =
    opt[Option[String]](name = VIEW,
        description = descriptionWithDefault(
            s"the state view to use with --$MAX_ERROR=n",
            configDefaults.checker.view,
        ), default = None)

  var outputTraces: Option[Boolean] =
    opt[Option[Boolean]](name = OUTPUT_TRACES,
        description = descriptionWithDefault(
            "save an example trace for each symbolic run",
          configDefaults.checker.outputTraces,
        ), default = None)

  var timeoutSmtSec: Option[Int] =
    opt[Option[Int]](name = TIMEOUT_SMT,
        description = descriptionWithDefault(
            "limit the duration of a single SMT check query with `n` seconds",
            configDefaults.checker.timeoutSmtSeconds,
        ) + " (unlimited)", default = None)

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val combinedTuningOptions =
      try {
        val loadedTuningOptions = tuningOptionsFile.map(f => loadProperties(f)).getOrElse(Map())
        overrideProperties(loadedTuningOptions, tuningOptions.getOrElse(""))
      } catch {
        case e: PassOptionException => return ConfigParseResult.failure(e.getMessage)
      }

    val base = super.toConfig
    if (!base.isSuccess) return ConfigParseResult.failureFrom(base)

    val tuning =
      if (combinedTuningOptions.nonEmpty) Some(combinedTuningOptions)
      else None
    val merged = mergeConfig(
        base,
        ApalacheConfig(
            checker = CheckerPatch(
                algorithm = algo,
              searchKind = Some(SearchKind.Check),
              seed = seed,
              outputTraces = outputTraces,
                smtSolver = smtSolver,
                smtEncoding = smtEncoding,
                tuning = tuning,
                discardDisabled = discardDisabled,
                checkDeadlocks = noDeadlocks.map(value => !value),
                maxError = maxError,
                timeoutSmtSeconds = timeoutSmtSec,
                view = view,
            )
        ),
    )

    warnIfTLCConfigIsPresent(merged.requireValue())
    merged
  }

  private def warnIfTLCConfigIsPresent(cfg: ApalacheConfig): Unit = {
    // The older versions of apalache were loading a TLC config file of
    // the same basename as the spec by default. We have flipped this
    // behavior in version 0.25.0. Hence, warn the user that their config
    // is not loaded by default.
    cfg.source.foreach {
      // The check is only relevant for TLA files
      case InputSource.FileSource(path, InputSource.Format.Tla) =>
        if (cfg.checker.tlcConfig.isEmpty) {
          val stem = FilenameUtils.removeExtension(path.getFileName.toString)
          val defaultConfig = new File(stem + ".cfg")
          if (defaultConfig.exists()) {
            val msg =
              s"  > TLC config file found in specification directory. To enable it, pass --$CONFIG=$defaultConfig."
            logger.info(msg)
          }
        }
      case _ => ()
    }

  }

  override def run(config: ApalacheConfig): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveCheck(config)) { options =>
      val tuning = options.checker.tuning
      logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

      PassChainExecutor(new CheckerModule(options)).run() match {
        case Right(_)      => Right(s"Checker reports no error up to computation length ${options.checker.length}")
        case Left(failure) => Left(failure.exitCode, "Checker has found an error")
      }
    }
  }

  private def loadProperties(filename: String): Map[String, String] = {
    // use an apache-commons library, as it supports variable substitution
    try {
      val config = new Configurations().properties(new File(filename))
      // access configuration properties
      var map = Map[String, String]()
      for (name: String <- config.getKeys.asScala) {
        map += (name -> config.getString(name))
      }
      // parse the properties and convert them back to strings for config serialization
      FineTuningParser.fromStrings(map) match {
        case Right(parsed) => parsed.view.mapValues(_.toString).toMap
        case Left(error)   => throw new PassOptionException(s"Error in the properties file $filename: $error")
      }
    } catch {
      case _: FileNotFoundException =>
        throw new PassOptionException(s"The properties file $filename not found")

      case e: ConfigurationException =>
        throw new PassOptionException(s"Error in the properties file $filename: ${e.getMessage}")
    }
  }

  private def overrideProperties(props: Map[String, String], propsAsString: String): Map[String, String] = {
    def parseKeyValue(text: String): (String, String) = {
      val parts = text.split('=')
      if (parts.length != 2 || parts.head.trim == "" || parts(1) == "") {
        throw new PassOptionException(s"Expected key=value in --$TUNING_OPTIONS=$propsAsString")
      } else {
        // trim to remove surrounding whitespace from the key, but allow the value to have white spaces
        (parts.head.trim, parts(1))
      }
    }

    val hereProps = {
      if (propsAsString.trim.nonEmpty) {
        // parse the properties and convert them back to strings for config serialization
        FineTuningParser.fromStrings(propsAsString.split(':').map(parseKeyValue).toMap) match {
          case Right(parsed) => parsed.view.mapValues(_.toString).toMap
          case Left(error)   => throw new PassOptionException(s"Error in the properties string $propsAsString: $error")
        }
      } else {
        Map.empty
      }
    }
    // hereProps may override the values in props
    props ++ hereProps
  }
}

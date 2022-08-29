package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.infra.PassOptionException
import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import java.io.{File, FileNotFoundException}
import org.apache.commons.configuration2.builder.fluent.Configurations
import org.apache.commons.configuration2.ex.ConfigurationException
import org.backuity.clist._
import org.backuity.clist.util.Read
import scala.jdk.CollectionConverters._
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.OptionGroup
import org.apache.commons.io.FilenameUtils

/**
 * This command initiates the 'check' command line.
 *
 * @author
 *   Igor Konnov
 */
class CheckCmd(name: String = "check", description: String = "Check a TLA+ specification")
    extends AbstractCheckerCmd(name, description) {

  // Parses the smtEncoding option
  implicit val smtEncodingRead: Read[SMTEncoding] =
    Read.reads[SMTEncoding]("a SMT encoding, either oopsla19 or arrays")(SMTEncoding.ofString)

  var nworkers: Option[Int] = opt[Option[Int]](name = "nworkers", default = None,
      description = "the number of workers for the parallel checker (soon), default: 1")
  var algo: Option[String] = opt[Option[String]](name = "algo", default = None,
      description = "the search algorithm: offline, incremental, parallel (soon), default: incremental")
  var smtEncoding: Option[SMTEncoding] = opt[Option[SMTEncoding]](name = "smt-encoding", useEnv = true, default = None,
      description =
        s"the SMT encoding: ${SMTEncoding.OOPSLA19}, ${SMTEncoding.Arrays} (experimental), ${SMTEncoding.FunArrays} (experimental), default: ${SMTEncoding.OOPSLA19} (overrides envvar SMT_ENCODING)")
  var tuningOptionsFile: Option[String] =
    opt[Option[String]](name = "tuning-options-file", default = None,
        description = "filename of the tuning options, see docs/tuning.md")
  var tuningOptions: Option[String] =
    opt[Option[String]](name = "tuning-options", default = None,
        description =
          "tuning options as arguments in the format key1=val1:key2=val2:key3=val3 (priority over --tuning-options-file)")
  var discardDisabled: Option[Boolean] = opt[Option[Boolean]](name = "discard-disabled", default = None,
      description =
        "pre-check, whether a transition is disabled, and discard it, to make SMT queries smaller, default: true")
  var noDeadlocks: Option[Boolean] =
    opt[Option[Boolean]](name = "no-deadlock", default = None,
        description = "do not check for deadlocks, default: false")

  var maxError: Option[Int] =
    opt[Option[Int]](name = "max-error",
        description =
          "do not stop on first error, but produce up to a given number of counterexamples (fine tune with --view), default: 1",
        default = None)

  var view: Option[String] =
    opt[Option[String]](name = "view",
        description = "the state view to use with --max-error=n, default: transition index", default = None)

  var saveRuns: Boolean =
    opt[Boolean](name = "output-traces", description = "save an example trace for each symbolic run, default: false",
        default = false)

  def collectTuningOptions(): Map[String, String] = {
    val tuning = tuningOptionsFile.map(f => loadProperties(f)).getOrElse(Map())
    overrideProperties(tuning, tuningOptions.getOrElse("")) ++ Map("search.outputTraces" -> saveRuns.toString)
  }

  override def toConfig(): Config.ApalacheConfig = {
    val cfg = super.toConfig()
    val newCfg = cfg.copy(
        checker = cfg.checker.copy(
            nworkers = nworkers,
            algo = algo,
            smtEncoding = smtEncoding,
            tuning = Some(collectTuningOptions()),
            discardDisabled = discardDisabled,
            noDeadlocks = noDeadlocks,
            maxError = maxError,
            view = view,
        ),
        typechecker = cfg.typechecker.copy(
            inferpoly = Some(true)
        ),
    )

    cfg.common.inputfile.foreach { file =>
      if (newCfg.checker.config.isEmpty) {
        // The older versions of apalache were loading a TLC config file of the same basename as the spec.
        // We have flipped this behavior in version 0.25.0.
        // Hence, warn the user that their config is not loaded by default.
        val stem = FilenameUtils.removeExtension(file.getName())
        val defaultConfig = new File(stem + ".cfg")
        if (defaultConfig.exists()) {
          val msg =
            s"  > TLC config file found in specification directory. To enable it, pass --config=$defaultConfig."
          logger.info(msg)
        }
      }
    }

    newCfg
  }

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithCheckerPreds(cfg).get
    val executor = Executor(new CheckerModule(options))

    val tuning = options.checker.tuning

    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    executor.run() match {
      case Right(_)   => Right(s"Checker reports no error up to computation length ${options.checker.length}")
      case Left(code) => Left(code, "Checker has found an error")
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
      map
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
        throw new PassOptionException(s"Expected key=value in --tuning-options=$propsAsString")
      } else {
        // trim to remove surrounding whitespace from the key, but allow the value to have white spaces
        (parts.head.trim, parts(1))
      }
    }

    val hereProps = {
      if (propsAsString.trim.nonEmpty) {
        propsAsString.split(':').map(parseKeyValue).toMap
      } else {
        Map.empty
      }
    }
    // hereProps may override the values in props
    props ++ hereProps
  }
}

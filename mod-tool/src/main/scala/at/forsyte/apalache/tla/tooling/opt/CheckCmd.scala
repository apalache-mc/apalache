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

/**
 * This command initiates the 'check' command line.
 *
 * @author
 *   Igor Konnov
 */
class CheckCmd(name: String = "check", description: String = "Check a TLA+ specification")
    extends AbstractCheckerCmd(name, description) {

  val executor = Executor(new CheckerModule)

  // Parses the smtEncoding option
  implicit val smtEncodingRead: Read[SMTEncoding] =
    Read.reads[SMTEncoding]("a SMT encoding, either oopsla19 or arrays")(SMTEncoding.ofString)

  var nworkers: Int = opt[Int](name = "nworkers", default = 1,
      description = "the number of workers for the parallel checker (soon), default: 1")
  var algo: String = opt[String](name = "algo", default = "incremental",
      description = "the search algorithm: offline, incremental, parallel (soon), default: incremental")
  var smtEncoding: SMTEncoding = opt[SMTEncoding](name = "smt-encoding", useEnv = true, default = SMTEncoding.Oopsla19,
      description =
        s"the SMT encoding: ${SMTEncoding.Oopsla19}, ${SMTEncoding.Arrays} (experimental), default: ${SMTEncoding.Oopsla19} (overrides envvar SMT_ENCODING)")
  var tuningOptionsFile: String =
    opt[String](name = "tuning-options-file", default = "",
        description = "filename of the tuning options, see docs/tuning.md")
  var tuningOptions: String =
    opt[String](name = "tuning-options", default = "",
        description =
          "tuning options as arguments in the format key1=val1:key2=val2:key3=val3 (priority over --tuning-options-file)")
  var discardDisabled: Boolean = opt[Boolean](name = "discard-disabled", default = true,
      description =
        "pre-check, whether a transition is disabled, and discard it, to make SMT queries smaller, default: true")
  var noDeadlocks: Boolean =
    opt[Boolean](name = "no-deadlock", default = false, description = "do not check for deadlocks, default: false")

  var maxError: Int =
    opt[Int](name = "max-error",
        description =
          "do not stop on first error, but produce up to a given number of counterexamples (fine tune with --view), default: 1",
        default = 1)

  var view: String =
    opt[String](name = "view", description = "the state view to use with --max-error=n, default: transition index",
        default = "")

  def collectTuningOptions(): Map[String, String] = {
    val tuning =
      if (tuningOptionsFile != "") loadProperties(tuningOptionsFile) else Map[String, String]()
    overrideProperties(tuning, tuningOptions)
  }

  def run() = {

    val tuning = collectTuningOptions()

    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    executor.passOptions.set("general.tuning", tuning)
    executor.passOptions.set("checker.nworkers", nworkers)
    executor.passOptions.set("checker.discardDisabled", discardDisabled)
    executor.passOptions.set("checker.noDeadlocks", noDeadlocks)
    executor.passOptions.set("checker.algo", algo)
    executor.passOptions.set("checker.smt-encoding", smtEncoding)
    executor.passOptions.set("checker.maxError", maxError)
    if (view != "")
      executor.passOptions.set("checker.view", view)
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    executor.passOptions.set("typechecker.inferPoly", true)
    setCommonOptions()
    executor.run() match {
      case Right(_)   => Right("Checker reports no error up to computation length " + length)
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

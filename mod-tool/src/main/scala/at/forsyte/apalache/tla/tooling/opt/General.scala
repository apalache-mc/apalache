package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist._

/**
 * The general commands.
 *
 * See: https://github.com/backuity/clist
 *
 * @author Igor Konnov
 */
trait General extends Command {
  var debug = opt[Boolean](description = "extensive logging in detailed.log and log.smt, default: false")
  var smtprof = opt[Boolean](description = "profile SMT constraints in log.smt, default: false")

  private var _invocation = ""
  private var _env = ""

  private def getOptionEnvVar(option: CliOption[_]) : Option[String] = {
    var envVar = option.name.replace("-", "_").toUpperCase()
    sys.env.get(envVar).map(value => s"${envVar}=${value}")
  }

  /** A verbatim representation of the command line arguments given when invoking the command */
  def invocation : String = _invocation

  /** CLI options that are set through environment variables */
  def env : String = _env

  override def read(args : List[String]) = {
    _env = super
      .options
      .filter(_.useEnv.getOrElse(false))
      .flatMap(getOptionEnvVar)
      .mkString(" ")

    _invocation = args.mkString(" ")

    super.read(args)
  }
}

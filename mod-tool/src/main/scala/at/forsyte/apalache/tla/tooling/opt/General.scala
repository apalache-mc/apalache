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

  private var _invocation : String = ""
  /** A verbatim representation of the command line arguments given when invoking the command */
  def invocation : String = _invocation
  override def read(args : List[String]) = {
    _invocation = args.reduce((a, b) => s"$a $b")
    super.read(args)
  }
}

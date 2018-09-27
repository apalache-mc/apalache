package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist._

/**
  * The general commands.
  *
  * See: https://github.com/backuity/clist
  *
  * @author Igor Konnov
  *
  */
trait General {
  this: Command =>
    var debug = opt[Boolean](description = "extensive logging in detailed.log and log.smt, default: false")
    var smtprof = opt[Boolean](description = "profile SMT constraints -- profile check-sat and write it in log.smt, default: false")
}

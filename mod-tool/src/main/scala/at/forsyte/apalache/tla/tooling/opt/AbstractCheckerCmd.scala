package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{arg, opt}

import java.io.File
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.SourceOption

// Holds the minimal necessary info about a specification.
abstract class AbstractCheckerCmd(val name: String, description: String)
    extends PassExecutorCmd(name, description) with LazyLogging {
  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var config: String = opt[String](name = "config", default = "", description = "configuration file in TLC format")
  var cinit: String = opt[String](name = "cinit", default = "",
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")
  var init: String = opt[String](name = "init", default = "",
      description = "the name of an operator that initializes VARIABLES,\n" +
        "default: Init")
  var next: String =
    opt[String](name = "next", default = "", description = "the name of a transition operator, default: Next")
  var inv: String =
    opt[String](name = "inv", default = "", description = "the name of an invariant operator, e.g., Inv")
  var temporal: String =
    opt[String](name = "temporal", default = "", description = "the name of a temporal property, e.g. Property")
  var length: Int =
    opt[Int](name = "length", default = 10, description = "maximal number of Next steps, default: 10")

  override def setCommonOptions(): Unit = {
    super.setCommonOptions()
    logger.info {
      val environment = if (env != "") s"(${env}) " else ""
      s"Checker options: ${environment}${name} ${invocation}"
    }
    executor.passOptions.set("parser.source", SourceOption.FileSource(file.getAbsoluteFile))
    if (config != "")
      executor.passOptions.set("checker.config", config)
    if (init != "")
      executor.passOptions.set("checker.init", init)
    if (next != "")
      executor.passOptions.set("checker.next", next)
    if (inv != "")
      executor.passOptions.set("checker.inv", List(inv))
    if (temporal != "")
      executor.passOptions.set("checker.temporal", List(temporal))
    if (cinit != "")
      executor.passOptions.set("checker.cinit", cinit)
    executor.passOptions.set("checker.length", length)
  }
}

package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{arg, opt}

import java.io.File
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.io.ConfigurationError

// Holds the minimal necessary info about a specification.
abstract class AbstractCheckerCmd(val name: String, description: String)
    extends PassExecutorCmd(name, description) with LazyLogging {
  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var config: Option[String] =
    opt[Option[String]](name = "config", default = None, description = "configuration file in TLC format")
  var cinit: Option[String] = opt[Option[String]](name = "cinit", default = None,
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")
  var init: Option[String] = opt[Option[String]](name = "init", default = None,
      description = "the name of an operator that initializes VARIABLES,\n" +
        "default: Init")
  var next: Option[String] =
    opt[Option[String]](name = "next", default = None, description = "the name of a transition operator, default: Next")
  var inv: Option[String] =
    opt[Option[String]](name = "inv", default = None, description = "the name of an invariant operator, e.g., Inv")
  var temporal: Option[String] =
    opt[Option[String]](name = "temporal", default = None,
        description = "the name of a temporal property, e.g. Property")
  var length: Option[Int] =
    opt[Option[Int]](name = "length", default = None, description = "maximal number of Next steps, default: 10")

  override def toConfig(): Config.ApalacheConfig = {
    val cfg = super.toConfig()
    cfg.copy(
        common = cfg.common.copy(inputfile = Some(file)),
        checker = cfg.checker.copy(config = config, cinit = cinit, init = init, next = next, inv = inv,
            temporal = temporal, length = length),
    )
  }
  override def setCommonOptions(): Unit = {
    // TODO: rm once OptionProvider is wired in
    val cfg = configuration.left.map(err => new ConfigurationError(err)).toTry.get

    super.setCommonOptions()
    logger.info {
      val environment = if (env != "") s"(${env}) " else ""
      s"Checker options: ${environment}${name} ${invocation}"
    }
    executor.passOptions.set("parser.source", SourceOption.FileSource(cfg.common.inputfile.get.getAbsoluteFile))
    cfg.checker.config.foreach(executor.passOptions.set("checker.config", _))
    cfg.checker.init.foreach(executor.passOptions.set("checker.init", _))
    cfg.checker.next.foreach(executor.passOptions.set("checker.next", _))
    cfg.checker.inv.foreach(inv => executor.passOptions.set("checker.inv", List(inv)))
    cfg.checker.temporal.foreach(temporal => executor.passOptions.set("checker.temporal", List(temporal)))
    cfg.checker.cinit.foreach(executor.passOptions.set("checker.cinit", _))
    executor.passOptions.set("checker.length", cfg.checker.length.get)
  }
}

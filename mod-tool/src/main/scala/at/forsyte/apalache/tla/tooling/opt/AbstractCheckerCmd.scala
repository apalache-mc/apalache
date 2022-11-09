package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{arg, opt}

import java.io.File
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.SourceOption
import scala.util.Try

// Holds the minimal necessary info about a specification.
abstract class AbstractCheckerCmd(val name: String, description: String)
    extends ApalacheCommand(name, description) with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var config =
    opt[Option[File]](name = "config", default = None, description = "configuration file in TLC format")
  var cinit: Option[String] = opt[Option[String]](name = "cinit", default = None,
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")
  var init: Option[String] = opt[Option[String]](name = "init", default = None,
      description = "the name of an operator that initializes VARIABLES,\n" +
        "default: Init")
  var next: Option[String] =
    opt[Option[String]](name = "next", default = None, description = "the name of a transition operator, default: Next")
  var inv =
    opt[Option[List[String]]](name = "inv", default = None,
        description = "the names of invariant operators, e.g., 'Inv' or 'InvA,InvB'")
  var temporal = opt[Option[List[String]]](name = "temporal", default = None,
      description = "the names of temporal properties, e.g. 'Property' or 'PropertyA,PropertyB'")
  var length: Option[Int] =
    opt[Option[Int]](name = "length", default = None, description = "maximal number of Next steps, default: 10")

  override def toConfig(): Try[Config.ApalacheConfig] = for {
    cfg <- super.toConfig()
    fileSource <- SourceOption.FileSource(file)
  } yield cfg.copy(
      input = cfg.input.copy(source = Some(fileSource)),
      checker = cfg.checker.copy(
          config = config,
          cinit = cinit,
          init = init,
          next = next,
          inv = inv,
          temporalProps = temporal,
          length = length,
      ),
  )

}

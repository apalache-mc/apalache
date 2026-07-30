package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{arg, opt}

import java.io.File
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver, CheckerPatch, ConfigParseResult}

// Holds the minimal necessary info about a specification.
abstract class AbstractCheckerCmd(val name: String, description: String)
    extends ApalacheCommand(name, description) with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var config =
    opt[Option[File]](name = "config", default = None,
        description = descriptionWithDefault(
            "configuration file in TLC format",
            configDefaults.checker.tlcConfig,
        ))
  var cinit: Option[String] = opt[Option[String]](name = "cinit", default = None,
      description = descriptionWithDefault(
          "the name of an operator that initializes CONSTANTS",
          configDefaults.checker.constantInitializer,
      ))
  var init: Option[String] = opt[Option[String]](name = "init", default = None,
      description = descriptionWithDefault(
          "the name of an operator that initializes VARIABLES",
          ApalacheConfigResolver.defaultInit,
      ))
  var next: Option[String] =
    opt[Option[String]](name = "next", default = None,
        description = descriptionWithDefault(
            "the name of a transition operator",
            ApalacheConfigResolver.defaultNext,
        ))
  var inv =
    opt[Option[List[String]]](name = "inv", default = None,
        description = descriptionWithDefault(
            "the names of invariant operators, e.g., 'Inv' or 'InvA,InvB'",
            configDefaults.checker.invariants,
        ))
  var temporal = opt[Option[List[String]]](name = "temporal", default = None,
      description = descriptionWithDefault(
          "the names of temporal properties, e.g. 'Property' or 'PropertyA,PropertyB'",
          configDefaults.checker.temporalProperties,
      ))
  var length: Option[Int] =
    opt[Option[Int]](name = "length", default = None,
        description = descriptionWithDefault(
            "maximal number of Next steps",
            configDefaults.checker.length,
        ))

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val base = super.toConfig
    if (!base.isSuccess) return ConfigParseResult.failureFrom(base)

    val fileSource = InputSource.FileSource(file)
    if (!fileSource.isSuccess) return ConfigParseResult.failureFrom(fileSource)

    mergeConfig(
        base,
        ApalacheConfig(
            source = Some(fileSource.requireValue()),
            checker = CheckerPatch(
                tlcConfig = config.map(_.toPath),
                constantInitializer = cinit,
                init = init,
                next = next,
                invariants = inv,
                temporalProperties = temporal,
                length = length,
            ),
        ),
    )
  }

}

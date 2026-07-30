package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.config.Constants._
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver, CheckerPatch, ConfigParseResult}
import com.typesafe.scalalogging.LazyLogging
import org.backuity.clist.{arg, opt}

import java.io.File

// Holds the minimal necessary info about a specification.
abstract class AbstractCheckerCmd(val name: String, description: String)
    extends ApalacheCommand(name, description) with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var config =
    opt[Option[File]](name = CONFIG, default = None,
        description = descriptionWithDefault(
            "configuration file in TLC format",
            configDefaults.checker.tlcConfig,
        ))
  var cinit: Option[String] = opt[Option[String]](name = CINIT, default = None,
      description = descriptionWithDefault(
          "the name of an operator that initializes CONSTANTS",
          configDefaults.checker.constantInitializer,
      ))
  var init: Option[String] = opt[Option[String]](name = INIT, default = None,
      description = descriptionWithDefault(
          "the name of an operator that initializes VARIABLES",
          ApalacheConfigResolver.defaultInit,
      ))
  var next: Option[String] =
    opt[Option[String]](name = NEXT, default = None,
        description = descriptionWithDefault(
            "the name of a transition operator",
            ApalacheConfigResolver.defaultNext,
        ))
  var inv =
    opt[Option[List[String]]](name = INV, default = None,
        description = descriptionWithDefault(
            "the names of invariant operators, e.g., 'Inv' or 'InvA,InvB'",
            configDefaults.checker.invariants,
        ))
  var temporal = opt[Option[List[String]]](name = TEMPORAL, default = None,
      description = descriptionWithDefault(
          "the names of temporal properties, e.g. 'Property' or 'PropertyA,PropertyB'",
          configDefaults.checker.temporalProperties,
      ))
  var length: Option[Int] =
    opt[Option[Int]](name = LENGTH, default = None,
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

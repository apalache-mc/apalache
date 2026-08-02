package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.{InputSource, OutputManager}
import at.forsyte.apalache.io.config.Constants.{INFER_POLY, OUTPUT, TYPECHECK}
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver, ConfigParseResult, TypecheckerPatch}
import at.forsyte.apalache.tla.passes.typecheck.TypeCheckerModule
import com.typesafe.scalalogging.LazyLogging
import org.backuity.clist._

import java.io.File

/**
 * This command initiates the 'typecheck' command line.
 *
 * @author
 *   Igor Konnov
 */
class TypeCheckCmd
    extends ApalacheCommand(name = TYPECHECK, description = "Check types in a TLA+ specification") with LazyLogging {

  var file: File = arg[File](description = "a TLA+ specification (.tla or .json)")
  var inferPoly: Option[Boolean] = opt[Option[Boolean]](name = INFER_POLY, default = None,
      description = descriptionWithDefault(
          "allow the type checker to infer polymorphic types",
          configDefaults.typechecker.inferPoly,
      ))
  var output: Option[File] = opt[Option[File]](name = OUTPUT,
      description = descriptionWithDefault(
          "file to which the typechecked source is written (.tla or .json)",
          configDefaults.output,
      ))

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val base = super.toConfig
    if (!base.isSuccess) {
      ConfigParseResult.failureFrom(base)
    } else {
      val source = InputSource.FileSource(file)
      if (!source.isSuccess) {
        ConfigParseResult.failureFrom(source)
      } else {
        mergeConfig(
            base,
            ApalacheConfig(
                source = Some(source.requireValue()),
                output = output.map(_.toPath),
                typechecker = TypecheckerPatch(inferPoly),
            ),
        )
      }
    }
  }

  override def run(config: ApalacheConfig, outputManager: OutputManager): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveTypecheck(config)) { options =>
      logger.info("Type checking " + file)
      PassChainExecutor(new TypeCheckerModule(options, outputManager)).run() match {
        case Right(_)      => Right("Type checker [OK]")
        case Left(failure) => Left(failure.exitCode, "Type checker [FAILED]")
      }
    }
  }
}

package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.{InputSource, OutputWorkspace}
import at.forsyte.apalache.io.config.Constants.{OUTPUT, PARSE}
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver, ConfigParseResult}
import at.forsyte.apalache.tla.passes.imp.ParserModule
import com.typesafe.scalalogging.LazyLogging
import org.backuity.clist._

import java.io.File

/**
 * This command initiates the 'parse' command line.
 *
 * @author
 *   Igor Konnov
 */
class ParseCmd
    extends ApalacheCommand(name = PARSE, description = "Parse a TLA+ specification and quit") with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var output: Option[File] = opt[Option[File]](name = OUTPUT,
      description = descriptionWithDefault(
          "file to which the parsed source is written (.tla or .json)",
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
            ),
        )
      }
    }
  }

  override def run(config: ApalacheConfig, outputWorkspace: OutputWorkspace): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveParse(config)) { options =>
      logger.info("Parse " + file)
      PassChainExecutor(new ParserModule(options, outputWorkspace)).run() match {
        case Right(m) =>
          Right(s"Parsed successfully\nRoot module: ${m.name} with ${m.declarations.length} declarations.")
        case Left(failure) => Left(failure.exitCode, "Parser has failed")
      }
    }
  }
}

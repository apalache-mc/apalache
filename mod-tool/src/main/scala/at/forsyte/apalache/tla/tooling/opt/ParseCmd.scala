package at.forsyte.apalache.tla.tooling.opt

import java.io.File
import org.backuity.clist._
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.tla.passes.imp.ParserModule

/**
 * This command initiates the 'parse' command line.
 *
 * @author
 *   Igor Konnov
 */
class ParseCmd
    extends ApalacheCommand(name = "parse", description = "Parse a TLA+ specification and quit") with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var output: Option[File] = opt[Option[File]](name = "output",
      description = "file to which the parsed source is written (.tla or .json), default: None")

  override def toConfig() = {
    val cfg = super.toConfig()
    cfg.copy(input = cfg.input.copy(source = Some(SourceOption.FileSource(file))),
        output = cfg.output.copy(output = output))
  }

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithIO(cfg).get

    logger.info("Parse " + file)

    PassChainExecutor.run(new ParserModule(options)) match {
      case Right(m) => Right(s"Parsed successfully\nRoot module: ${m.name} with ${m.declarations.length} declarations.")
      case Left(failure) => Left(failure.exitCode, "Parser has failed")
    }
  }
}

package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist._
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.infra.passes.options.SourceOption

/**
 * This command initiates the 'parse' command line.
 *
 * @author
 *   Igor Konnov
 */
class ParseCmd
    extends PassExecutorCmd(name = "parse", description = "Parse a TLA+ specification and quit") with LazyLogging {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var output: Option[String] = opt[Option[String]](name = "output",
      description = "file to which the parsed source is written (.tla or .json), default: None")

  val executor = Executor(new ParserModule)

  def run() = {
    logger.info("Parse " + file)

    executor.passOptions.set("parser.source", SourceOption.FileSource(file.getAbsoluteFile))
    output.foreach(executor.passOptions.set("io.output", _))

    setCommonOptions()

    executor.run() match {
      case Right(m) => Right(s"Parsed successfully\nRoot module: ${m.name} with ${m.declarations.length} declarations.")
      case Left(code) => Left(code, "Parser has failed")
    }
  }
}

package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.tla.typecheck.passes.TypeCheckerModule
import com.typesafe.scalalogging.LazyLogging

/**
 * This command initiates the 'typecheck' command line.
 *
 * @author
 *   Igor Konnov
 */
class TypeCheckCmd
    extends Command(name = "typecheck", description = "Check types in a TLA+ specification") with PassExecutorCmd
    with LazyLogging {

  val executor = Executor(new TypeCheckerModule)

  var file: File = arg[File](description = "a TLA+ specification (.tla or .json)")
  var inferPoly: Boolean = opt[Boolean](name = "infer-poly", default = true,
      description = "allow the type checker to infer polymorphic types, default: true")
  var output: Option[String] = opt[Option[String]](name = "output",
      description = "file to which the typechecked source is written (.tla or .json), default: None")

  override def run() = {
    logger.info("Type checking " + file)
    executor.passOptions.set("parser.filename", file.getAbsolutePath)
    output.foreach(executor.passOptions.set("io.output", _))
    executor.passOptions.set("typechecker.inferPoly", inferPoly)
    setCommonOptions()
    executor.run() match {
      case Right(_)   => Right("Type checker [OK]")
      case Left(code) => Left(code, "Type checker [FAILED]")
    }
  }
}

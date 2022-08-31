package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist._
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.tla.typecheck.passes.TypeCheckerModule
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.options.SourceOption

/**
 * This command initiates the 'typecheck' command line.
 *
 * @author
 *   Igor Konnov
 */
class TypeCheckCmd
    extends ApalacheCommand(name = "typecheck", description = "Check types in a TLA+ specification") with LazyLogging {

  var file: File = arg[File](description = "a TLA+ specification (.tla or .json)")
  var inferPoly: Option[Boolean] = opt[Option[Boolean]](name = "infer-poly", default = None,
      description = "allow the type checker to infer polymorphic types, default: true")
  var output: Option[File] = opt[Option[File]](name = "output",
      description = "file to which the typechecked source is written (.tla or .json), default: None")

  override def toConfig(): Config.ApalacheConfig = {
    val cfg = super.toConfig()
    cfg.copy(
        input = cfg.input.copy(source = Some(SourceOption.FileSource(file))),
        output = cfg.output.copy(output = output),
        typechecker = cfg.typechecker.copy(inferpoly = inferPoly),
    )
  }
  override def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithTypechecker(cfg).get
    val executor = Executor(new TypeCheckerModule(options))

    logger.info("Type checking " + file)

    executor.run() match {
      case Right(_)   => Right("Type checker [OK]")
      case Left(code) => Left(code, "Type checker [FAILED]")
    }
  }
}

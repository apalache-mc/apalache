package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.bmcmt.config.ReTLAToVMTModule
import at.forsyte.apalache.tla.bmcmt.rules.vmt.TlaExToVMTWriter
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.PassChainExecutor

class TranspileCmd extends AbstractCheckerCmd(name = "transpile", description = "Transpile and quit") {

  override def toConfig() = super.toConfig().map { cfg =>
    cfg.copy(typechecker = cfg.typechecker.copy(inferpoly = Some(true)))
  }

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithCheckerPreds(cfg).get

    val outFilePath = OutputManager.runDirPathOpt
      .map { p =>
        p.resolve(TlaExToVMTWriter.outFileName).toAbsolutePath
      }
      .getOrElse(TlaExToVMTWriter.outFileName)

    PassChainExecutor(new ReTLAToVMTModule(options)).run() match {
      case Right(_)      => Right(s"VMT constraints successfully generated at\n$outFilePath")
      case Left(failure) => Left(failure.exitCode, "Failed to generate constraints")
    }
  }
}

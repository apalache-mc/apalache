package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.config.Constants.TRANSPILE
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver}
import at.forsyte.apalache.tla.bmcmt.config.ReTLAToVMTModule
import at.forsyte.apalache.tla.bmcmt.rules.vmt.TlaExToVMTWriter

class TranspileCmd extends AbstractCheckerCmd(name = TRANSPILE, description = "Transpile and quit") {

  override def run(config: ApalacheConfig): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveCheck(config)) { options =>
      val outFilePath = OutputManager.pathInRunDir(TlaExToVMTWriter.outFileName).toAbsolutePath

      PassChainExecutor(new ReTLAToVMTModule(options)).run() match {
        case Right(_)      => Right(s"VMT constraints successfully generated at\n$outFilePath")
        case Left(failure) => Left(failure.exitCode, "Failed to generate constraints")
      }
    }
  }
}

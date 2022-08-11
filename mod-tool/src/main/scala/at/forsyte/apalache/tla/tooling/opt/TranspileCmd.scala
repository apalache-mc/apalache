package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.bmcmt.config.ReTLAToVMTModule
import at.forsyte.apalache.tla.bmcmt.rules.vmt.TlaExToVMTWriter

class TranspileCmd extends AbstractCheckerCmd(name = "transpile", description = "Transpile and quit") {
  val executor = Executor(new ReTLAToVMTModule)

  def run() = {
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    // TODO pass options
    executor.passOptions.set("typechecker.inferPoly", true)
    setCommonOptions()
    val outFilePath = OutputManager.runDirPathOpt
      .map { p =>
        p.resolve(TlaExToVMTWriter.outFileName).toAbsolutePath
      }
      .getOrElse(TlaExToVMTWriter.outFileName)
    executor.run() match {
      case Right(_)   => Right(s"VMT constraints successfully generated at\n$outFilePath")
      case Left(code) => Left(code, "Failed to generate constraints")
    }
  }
}

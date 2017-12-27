package at.forsyte.apalache.infra.passes
import at.forsyte.apalache.tla.lir.TlaModule

class TerminalPassWithTlaModule extends TerminalPass with TlaModuleMixin {
  var tlaModule: Option[TlaModule] = None
}

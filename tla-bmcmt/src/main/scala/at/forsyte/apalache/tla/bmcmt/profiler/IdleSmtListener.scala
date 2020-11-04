package at.forsyte.apalache.tla.bmcmt.profiler
import at.forsyte.apalache.tla.lir.TlaEx

class IdleSmtListener extends SmtListener {
  override def onIntroSmtConst(name: String): Unit = {}

  override def onIntroCell(id: Long): Unit = {}

  override def onSmtAssert(e: TlaEx, nSmtNodes: Long): Unit = {}
}

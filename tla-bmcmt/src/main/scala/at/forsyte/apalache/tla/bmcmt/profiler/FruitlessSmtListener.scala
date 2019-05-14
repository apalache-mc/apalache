package at.forsyte.apalache.tla.bmcmt.profiler
import at.forsyte.apalache.tla.lir.TlaEx

class FruitlessSmtListener extends SmtListener {
  override def onIntroSmtConst(name: String): Unit = {}

  override def onIntroCell(id: Long): Unit = {}

  override def onSmtAssert(e: TlaEx): Unit = {}
}

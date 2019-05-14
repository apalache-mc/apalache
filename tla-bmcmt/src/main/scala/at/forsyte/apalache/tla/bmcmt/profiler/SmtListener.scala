package at.forsyte.apalache.tla.bmcmt.profiler
import at.forsyte.apalache.tla.lir.TlaEx

trait SmtListener {

  def onIntroSmtConst(name: String): Unit

  def onIntroCell(id: Long): Unit

  def onSmtAssert(e: TlaEx): Unit
}

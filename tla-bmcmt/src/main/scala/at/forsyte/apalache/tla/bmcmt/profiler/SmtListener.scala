package at.forsyte.apalache.tla.bmcmt.profiler
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * An abstract listener that helps us to collect useful metrics.
 *
 * @author Igor Konnov
 */
trait SmtListener {

  /**
   * This method is called whenever a new SMT constant is introduced.
   * @param name the constant name
   */
  def onIntroSmtConst(name: String): Unit

  /**
   * This method is called whenever a new arena cell is introduced at the SMT level.
   * @param id the cell id
   */
  def onIntroCell(id: Long): Unit

  /**
   * This method is called whenever a new SMT assertion has been added.
   * @param ex assertion encoded as the TLA IR
   * @param nSmtNodes the number of syntactic nodes that are created in the SMT context when translating ex
   */
  def onSmtAssert(ex: TlaEx, nSmtNodes: Long): Unit
}

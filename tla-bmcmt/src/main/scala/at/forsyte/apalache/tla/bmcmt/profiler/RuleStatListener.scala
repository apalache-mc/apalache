package at.forsyte.apalache.tla.bmcmt.profiler

import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * A listener that keeps a stack of rule statistics entries and updates the statistics on respective calls.
  *
  * @author Igor Konnov
  */
class RuleStatListener extends SmtListener {
  val locator = new RuleStatLocator()
  private var stack: Seq[RuleStat] = Seq()

  def enterRule(ruleName: String): Unit = {
    val stat = locator.getRuleStat(ruleName)
    stat.nCalls += 1
    stack = stat +: stack
  }

  def exitRule(): Unit = {
    assert(stack.nonEmpty)
    stack = stack.tail
  }

  override def onIntroSmtConst(name: String): Unit = {
    if (stack.nonEmpty)
      stack.head.nSmtConstsSelf += 1
  }

  override def onIntroCell(id: Long): Unit = {
    if (stack.nonEmpty)
      stack.head.nCellsSelf += 1
  }

  override def onSmtAssert(e: TlaEx): Unit = {
    if (stack.nonEmpty) {
      stack.head.nSmtAssertsSelf += 1
      stack.head.smtAssertsSizeTotal += exprSize(e)
    }
  }

  private def exprSize(e: TlaEx): Int = {
    e match {
      case OperEx(_, args @ _*) => 1 + (args map exprSize).sum
      case _ => 1
    }
  }
}

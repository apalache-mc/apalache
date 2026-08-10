package at.forsyte.apalache.tla.bmcmt.profiler

import at.forsyte.apalache.io.OutputWorkspace

import scala.collection.immutable.SortedMap

/**
 * The locator keeps a registry of RuleStat instances -- one per rule name -- and finds the required instances when
 * needed.
 *
 * @author
 *   Igor Konnov
 */
class RuleStatLocator(outputWorkspace: Option[OutputWorkspace] = None) {
  private var ruleStats: Map[String, RuleStat] = Map()

  def getRuleStat(ruleName: String): RuleStat = {
    ruleStats.get(ruleName) match {
      case Some(r) => r
      case None    =>
        val newRule = new RuleStat(ruleName)
        ruleStats += ruleName -> newRule
        newRule
    }
  }

  def getStats = SortedMap(ruleStats.toSeq: _*)

  def writeStats(): Unit =
    outputWorkspace.foreach(_.withProfilingWriter { writer =>
      def writeLine(line: String): Unit = {
        writer.write(line)
        writer.newLine()
      }

      writeLine("Rule profiling statistics")
      val hrule = List.fill(80)('-').mkString
      writeLine(hrule)
      writeLine("%20s %9s %9s %9s %9s %9s"
            .format("name", "calls", "cells", "smt-consts", "smt-asserts", "smt-avg-size"))
      writeLine(hrule)
      val stats = ruleStats.values.toSeq.sortWith(_.nCalls > _.nCalls)
      for (rs <- stats) {
        writeLine("%-20s %9d %9d %9d %9d %9d"
              .format(
                  rs.ruleName,
                  rs.nCalls,
                  rs.nCellsSelf,
                  rs.nSmtConstsSelf,
                  rs.nSmtAssertsSelf,
                  rs.smtAssertsSizeAvg,
              ))
      }
    })
}

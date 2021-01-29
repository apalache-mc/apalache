package at.forsyte.apalache.tla.bmcmt.profiler

import java.io.{BufferedWriter, FileWriter, PrintWriter}

import scala.collection.immutable.SortedMap

/**
  * The locator keeps a registry of RuleStat instances
  * -- one per rule name -- and finds the required instances when needed.
  *
  * @author Igor Konnov
  */
class RuleStatLocator {
  private var ruleStats: Map[String, RuleStat] = Map()

  def getRuleStat(ruleName: String): RuleStat = {
    ruleStats.get(ruleName) match {
      case Some(r) => r
      case None =>
        val newRule = new RuleStat(ruleName)
        ruleStats += ruleName -> newRule
        newRule
    }
  }

  def getStats = SortedMap(ruleStats.toSeq :_*)

  def writeStats(filename: String): Unit = {
    val writer = new PrintWriter(new FileWriter(filename, false))
    writer.println("Rule profiling statistics")
    val hrule = List.fill(80)('-').mkString
    writer.println(hrule)
    writer.println("%20s %9s %9s %9s %9s %9s"
      .format("name", "calls", "cells", "smt-consts", "smt-asserts", "smt-avg-size"))
    writer.println(hrule)
    val stats = ruleStats.values.toSeq.sortWith(_.nCalls > _.nCalls)
    for (rs <- stats) {
      writer.println("%-20s %9d %9d %9d %9d %9d"
        .format(rs.ruleName, rs.nCalls, rs.nCellsSelf, rs.nSmtConstsSelf, rs.nSmtAssertsSelf, rs.smtAssertsSizeAvg))
    }
    writer.close()
  }
}

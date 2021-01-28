package at.forsyte.apalache.tla.bmcmt.smt

/**
  * SMT metrics that are collected by an instance of SolverContext.
  *
  * @param nCells number of introduced arena cells
  * @param nConsts number of introduced SMT constants
  * @param nSmtExprs number of constructed SMT expressions (including subexpressions)
  *
  * @author Igor Konnov
  */
class SolverContextMetrics(val nCells: Long, val nConsts: Long, val nSmtExprs: Long) {
  /**
    * Compute the weight based on metrics. Currently, the metric equals to nCells + nConsts + sqrt(nSmtExprs).
    * If we find a better metric, we will change it.
    */
  lazy val weight: Long = nCells + nConsts + Math.sqrt(Math.max(0, nSmtExprs)).toLong

  def delta(earlier: SolverContextMetrics): SolverContextMetrics = {
    new SolverContextMetrics(nCells - earlier.nCells, nConsts - earlier.nConsts, nSmtExprs - earlier.nSmtExprs)
  }

  def add(delta: SolverContextMetrics): SolverContextMetrics = {
    new SolverContextMetrics(nCells + delta.nCells, nConsts + delta.nCells, nSmtExprs + delta.nSmtExprs)
  }

  def addNCells(num: Long): SolverContextMetrics = {
    new SolverContextMetrics(nCells + num, nConsts, nSmtExprs)
  }

  def addNConsts(num: Long): SolverContextMetrics = {
    new SolverContextMetrics(nCells, nConsts + num, nSmtExprs)
  }

  def addNSmtExprs(num: Long): SolverContextMetrics = {
    new SolverContextMetrics(nCells, nConsts, nSmtExprs + num)
  }
}

object SolverContextMetrics {
  def empty: SolverContextMetrics = {
    new SolverContextMetrics(0, 0, 0)
  }
}

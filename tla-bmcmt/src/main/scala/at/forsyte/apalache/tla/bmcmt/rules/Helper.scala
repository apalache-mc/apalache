package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{PredRex, Rex, SolverContext}

object Helper {
  def isFalse(ctx: SolverContext)(e: Rex): Boolean = {
    e match {
      case PredRex(name) => name == ctx.predFalse()
      case _ => false
    }
  }

  def isTrue(ctx: SolverContext)(e: Rex): Boolean = {
    e match {
      case PredRex(name) => name == ctx.predTrue()
      case _ => false
    }
  }

  def predRex_s(e: Rex): String = {
    e match {
      case PredRex(name) => name
      case _ => ""
    }
  }
}
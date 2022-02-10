package at.forsyte.apalache.tla.bmcmt.util

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.BuilderEx

// Singular constructor of `apalacheChain`
object ConsChainUtil {
  def consChainFold[T](seq: Seq[T], terminal: BuilderEx, opCondFn: T => (BuilderEx, BuilderEx)): BuilderEx =
    seq.foldRight(terminal) { case (cell, partial) =>
      val (op, cond) = opCondFn(cell)
      tla.apalacheChain(op, partial, cond)
    }
}

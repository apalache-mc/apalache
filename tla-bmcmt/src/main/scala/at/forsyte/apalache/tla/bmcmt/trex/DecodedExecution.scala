package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A symbolic execution that has been decoded from an SMT model.
  *
  * @param path the sequence of variables bindings and transition numbers, from the initial state to the final state
  *
  * @author Igor Konnov
  */
class DecodedExecution(val path: List[(Map[String, TlaEx], Int)])

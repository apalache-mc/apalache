package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.TlaEx

import scala.collection.immutable.HashMap

package object bmcmt {
  /**
    * Binding variables to memory cells.
    */
  type Binding = HashMap[String, ArenaCell]

  /**
    * Our symbolic machine receives and produces two kinds of rewriting expressions (REX):
    * (1) a TLA+ expression, and (2) a name of a Boolean variable that is equivalent to
    * the rewriting result in SMT.
    */
  abstract class Rex

  /**
    * A TLA+ expression.
    * @param tlaEx a TLA+ expression to be translated
    */
  case class TlaRex(tlaEx: TlaEx) extends Rex

  /**
    * A Boolean variable in SMT.
    * @param predName a variable name
    */
  case class PredRex(predName: String) extends Rex
}
package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.lir.formulas.Term

package object vmt {
  type Context = Map[String, Term]
}

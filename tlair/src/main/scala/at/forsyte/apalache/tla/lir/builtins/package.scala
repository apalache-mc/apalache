package at.forsyte.apalache.tla.lir

package builtins {

import at.forsyte.apalache.tla.lir.values.TlaBuiltinSet

case class TlaBoolSet(name: String = "BOOLEAN") extends TlaBuiltinSet

  case class TlaStrSet(name: String = "STRING") extends TlaBuiltinSet

  case class TlaIntSet(name: String = "Int") extends TlaBuiltinSet

  case class TlaNatSet(name: String = "Nat") extends TlaBuiltinSet

  case class TlaRealSet(name: String = "Real") extends TlaBuiltinSet
}

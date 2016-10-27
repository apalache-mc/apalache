package at.forsyte.apalache.tla.lir

package predef {
  import at.forsyte.apalache.tla.lir.values.TlaPredefSet

  case class TlaEmptySet(name: String = "EMPTY") extends TlaPredefSet

  case class TlaBoolSet(name: String = "BOOLEAN") extends TlaPredefSet

  case class TlaStrSet(name: String = "STRING") extends TlaPredefSet

  case class TlaIntSet(name: String = "Int") extends TlaPredefSet

  case class TlaNatSet(name: String = "Nat") extends TlaPredefSet

  case class TlaRealSet(name: String = "Real") extends TlaPredefSet
}

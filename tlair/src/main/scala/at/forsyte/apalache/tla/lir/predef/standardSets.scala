package at.forsyte.apalache.tla.lir.predef

import at.forsyte.apalache.tla.lir.values.TlaPredefSet

/**
  * The empty set (we assume that there is just one empty set).
  */
object TlaEmptySet extends TlaPredefSet {
  override val name: String = "EMPTY"
}

/**
  * The standard set of booleans. Of course, one can explicitly construct the set { FALSE, TRUE }.
  */
object TlaBoolSet extends TlaPredefSet {
  override val name: String = "BOOLEAN"
}

/**
  * The standard set of all strings.
  */
object TlaStrSet extends TlaPredefSet {
  override val name: String = "STRING"
}

/**
  * The standard set of all integers.
  */
object TlaIntSet extends TlaPredefSet {
  override val name: String = "Int"
}

/**
  * The standard set of all naturals, including zero.
  */
object TlaNatSet extends TlaPredefSet {
  override val name: String = "Nat"
}

/**
  * The standard set of all reals.
  */
object TlaRealSet extends TlaPredefSet {
  override val name: String = "Real"
}

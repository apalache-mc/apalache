package at.forsyte.apalache.tla.bmcmt

sealed trait InvariantKind

case object StateInvariant extends InvariantKind {
  override def toString(): String = "state"
}

case object ActionInvariant extends InvariantKind {
  override def toString(): String = "action"
}

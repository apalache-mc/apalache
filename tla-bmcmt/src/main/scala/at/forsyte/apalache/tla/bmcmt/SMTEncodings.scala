package at.forsyte.apalache.tla.bmcmt

sealed trait SMTEncoding

case object oopsla19Encoding extends SMTEncoding {
  override def toString: String = "oopsla19"
}
case object arraysEncoding extends SMTEncoding {
  override def toString: String = "arrays"
}

package at.forsyte.apalache.tla.bmcmt

object SMTEncodings extends Enumeration {
  type SMTEncoding = Value
  val oopsla19Encoding, arraysEncoding, invalidEncoding = Value
}

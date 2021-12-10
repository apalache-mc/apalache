package at.forsyte.apalache.tla.bmcmt

sealed trait SMTEncoding

case object oopsla19Encoding extends SMTEncoding
case object arraysEncoding extends SMTEncoding

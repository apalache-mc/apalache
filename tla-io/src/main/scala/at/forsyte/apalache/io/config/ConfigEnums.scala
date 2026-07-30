package at.forsyte.apalache.io.config

/** SMT encodings accepted by configuration inputs. */
sealed abstract class SMTEncoding(val name: String) {
  final override def toString: String = name
}

object SMTEncoding {
  case object OOPSLA19 extends SMTEncoding("oopsla19")
  case object Arrays extends SMTEncoding("arrays")
  case object FunArrays extends SMTEncoding("funArrays")

  /** Canonical values in user-facing order. */
  val values: List[SMTEncoding] = List(OOPSLA19, Arrays, FunArrays)

  def fromString(value: String): SMTEncoding =
    value match {
      case "arrays"                   => Arrays
      case "funArrays" | "fun-arrays" => FunArrays
      case "oopsla19" | "oopsla-19"   => OOPSLA19
      case other                      => throw new IllegalArgumentException(s"Unexpected SMT encoding: $other")
    }
}

/** Supported SMT solver backends. */
sealed abstract class SMTSolver(val name: String) {
  final override def toString: String = name
}

object SMTSolver {
  case object Z3 extends SMTSolver("z3")
  case object CVC5 extends SMTSolver("cvc5")

  /** Canonical values in user-facing order. */
  val values: List[SMTSolver] = List(Z3, CVC5)

  def fromString(value: String): SMTSolver =
    value.toLowerCase match {
      case "z3"   => Z3
      case "cvc5" => CVC5
      case other  => throw new IllegalArgumentException(s"Unexpected SMT solver backend: $other")
    }
}

/** Supported model-checking algorithms. */
sealed abstract class Algorithm(val name: String) {
  final override def toString: String = name
}

object Algorithm {
  case object Incremental extends Algorithm("incremental")
  case object Offline extends Algorithm("offline")
  case object Remote extends Algorithm("remote")

  /** Canonical values in user-facing order. */
  val values: List[Algorithm] = List(Incremental, Offline, Remote)

  def fromString(value: String): Algorithm =
    value.toLowerCase match {
      case "incremental" => Incremental
      case "offline"     => Offline
      case "remote"      => Remote
      case other         => throw new IllegalArgumentException(s"Unexpected checker algorithm: $other")
    }
}

/** Supported server implementations. */
sealed abstract class ServerType(val name: String) {
  final override def toString: String = name
}

object ServerType {
  case object Checker extends ServerType("checker")
  case object Explorer extends ServerType("explorer")

  /** Canonical values in user-facing order. */
  val values: List[ServerType] = List(Checker, Explorer)

  def fromString(value: String): ServerType =
    value.toLowerCase match {
      case "checker"  => Checker
      case "explorer" => Explorer
      case other      => throw new IllegalArgumentException(s"Unexpected server type: $other")
    }
}

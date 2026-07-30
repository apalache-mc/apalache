package at.forsyte.apalache.io.config

/** SMT encodings accepted by configuration inputs. */
sealed abstract class SMTEncoding(val name: String) {
  final override def toString: String = name
}

object SMTEncoding {
  case object OOPSLA19 extends SMTEncoding(Constants.OOPSLA19)

  case object Arrays extends SMTEncoding(Constants.ARRAYS)

  case object FunArrays extends SMTEncoding(Constants.FUN_ARRAYS)

  /** Canonical values in user-facing order. */
  val values: List[SMTEncoding] = List(OOPSLA19, Arrays, FunArrays)

  def fromString(value: String): SMTEncoding =
    value match {
      case Constants.ARRAYS                                  => Arrays
      case Constants.FUN_ARRAYS | Constants.FUN_ARRAYS_ALIAS => FunArrays
      case Constants.OOPSLA19 | Constants.OOPSLA19_ALIAS     => OOPSLA19
      case other => throw new IllegalArgumentException(s"Unexpected SMT encoding: $other")
    }
}

/** Supported SMT solver backends. */
sealed abstract class SMTSolver(val name: String) {
  final override def toString: String = name
}

object SMTSolver {
  case object Z3 extends SMTSolver(Constants.Z3)

  case object CVC5 extends SMTSolver(Constants.CVC5)

  /** Canonical values in user-facing order. */
  val values: List[SMTSolver] = List(Z3, CVC5)

  def fromString(value: String): SMTSolver =
    value.toLowerCase match {
      case Constants.Z3   => Z3
      case Constants.CVC5 => CVC5
      case other          => throw new IllegalArgumentException(s"Unexpected SMT solver backend: $other")
    }
}

/** Supported model-checking algorithms. */
sealed abstract class Algorithm(val name: String) {
  final override def toString: String = name
}

object Algorithm {
  case object Incremental extends Algorithm(Constants.INCREMENTAL)

  case object Offline extends Algorithm(Constants.OFFLINE)

  case object Remote extends Algorithm(Constants.REMOTE)

  /** Canonical values in user-facing order. */
  val values: List[Algorithm] = List(Incremental, Offline, Remote)

  def fromString(value: String): Algorithm =
    value.toLowerCase match {
      case Constants.INCREMENTAL => Incremental
      case Constants.OFFLINE     => Offline
      case Constants.REMOTE      => Remote
      case other                 => throw new IllegalArgumentException(s"Unexpected checker algorithm: $other")
    }
}

/** Supported server implementations. */
sealed abstract class ServerType(val name: String) {
  final override def toString: String = name
}

object ServerType {
  case object Checker extends ServerType(Constants.CHECKER)

  case object Explorer extends ServerType(Constants.EXPLORER)

  /** Canonical values in user-facing order. */
  val values: List[ServerType] = List(Checker, Explorer)

  def fromString(value: String): ServerType =
    value.toLowerCase match {
      case Constants.CHECKER  => Checker
      case Constants.EXPLORER => Explorer
      case other              => throw new IllegalArgumentException(s"Unexpected server type: $other")
    }
}

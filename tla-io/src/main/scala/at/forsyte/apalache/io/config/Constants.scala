package at.forsyte.apalache.io.config

/** Names shared by Apalache configuration files, command-line options, and service configuration. */
object Constants {
  // Commands and top-level sections. Some names intentionally serve both roles.
  val CHECK = "check"
  val CONFIG = "config"
  val PARSE = "parse"
  val SERVER = "server"
  val SIMULATE = "simulate"
  val TEST = "test"
  val TRACEE = "tracee"
  val TRANSPILE = "transpile"
  val TYPECHECK = "typecheck"

  // Top-level configuration fields.
  val CHECKER = "checker"
  val COMMAND = "command"
  val CONFIG_FILE = "config-file"
  val DEBUG = "debug"
  val FEATURES = "features"
  val OUTPUT = "output"
  val OUT_DIR = "out-dir"
  val PROFILING = "profiling"
  val RUN_DIR = "run-dir"
  val SMTPROF = "smtprof"
  val SOURCE = "source"
  val TYPECHECKER = "typechecker"
  val WRITE_INTERMEDIATE = "write-intermediate"

  // Checker fields.
  val ALGO = "algo"
  val CINIT = "cinit"
  val DISCARD_DISABLED = "discard-disabled"
  val INIT = "init"
  val INV = "inv"
  val LENGTH = "length"
  val MAX_ERROR = "max-error"
  val NEXT = "next"
  val NO_DEADLOCK = "no-deadlock"
  val SMT_ENCODING = "smt-encoding"
  val SMT_SOLVER = "smt-solver"
  val TEMPORAL = "temporal"
  val TIMEOUT_SMT = "timeout-smt"
  val TUNING = "tuning"
  val VIEW = "view"

  // Typechecker, trace, server, and source-object fields.
  val AUX = "aux"
  val CONTENT = "content"
  val EXPRESSIONS = "expressions"
  val FILE = "file"
  val FORMAT = "format"
  val INFER_POLY = "infer-poly"
  val IP = "ip"
  val KIND = "kind"
  val PATH = "path"
  val PORT = "port"
  val SERVER_TYPE = "server-type"
  val TRACE = "trace"

  // Source-object discriminators.
  val STRING = "string"

  // Enum values.
  val ARRAYS = "arrays"
  val CVC5 = "cvc5"
  val EXPLORER = "explorer"
  val FUN_ARRAYS = "funArrays"
  val INCREMENTAL = "incremental"
  val OFFLINE = "offline"
  val OOPSLA19 = "oopsla19"
  val REMOTE = "remote"
  val Z3 = "z3"

  // CLI-only option and argument names.
  val ACTION = "action"
  val ASSERTION = "assertion"
  val BEFORE = "before"
  val ENABLE_STATS = "enable-stats"
  val MAX_RUN = "max-run"
  val OUTPUT_TRACES = "output-traces"
  val TUNING_OPTIONS = "tuning-options"
  val TUNING_OPTIONS_FILE = "tuning-options-file"

  // Configuration discovery and JVM properties.
  val LEGACY_CONFIG_EXTENSION = ".cfg"
  val GLOBAL_CONFIG_FILENAME = "apalache.json"
  val JSON_EXTENSION = ".json"
  val LOCAL_CONFIG_FILENAME = ".apalache.json"
  val TLA_PLUS_DIRECTORY = ".tlaplus"
  val USER_HOME_PROPERTY = "user.home"
}

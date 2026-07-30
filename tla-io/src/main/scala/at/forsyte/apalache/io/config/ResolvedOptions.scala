package at.forsyte.apalache.io.config

import at.forsyte.apalache.infra.tlc.config.{BehaviorSpec, TlcConfig}
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.tla.lir.Feature

import java.nio.file.Path

/** Resolved settings shared by every execution mode. */
final case class CommonOptions(
    debug: Boolean,
    features: List[Feature],
    outDir: Path,
    profiling: Boolean,
    runDir: Option[Path],
    smtprof: Boolean,
    writeIntermediate: Boolean)

/** Values needed to initialize output and logging for a command. */
final case class CommandInitializationOptions(
    command: String,
    common: CommonOptions,
    source: Option[InputSource])

/** Input and output values injected into the frontend passes. */
final case class ModuleIoOptions(
    source: InputSource,
    output: Option[Path])

/** Resolved type-inference settings. */
final case class TypecheckerOptions(inferPoly: Boolean)

/** Resolved model-checker engine settings independent of the specification. */
final case class CheckerOptions(
    algorithm: Algorithm,
    discardDisabled: Boolean,
    length: Int,
    maxError: Int,
    timeoutSmtSeconds: Int,
    checkDeadlocks: Boolean,
    smtSolver: SMTSolver,
    smtEncoding: SMTEncoding,
    tuning: Map[String, String])

/** A parsed TLC configuration together with its source path. */
final case class TlcConfigInput(
    config: TlcConfig,
    path: Path)

/** Resolved behavior, properties, and TLC-derived specification settings. */
final case class SpecificationOptions(
    behaviorSpec: BehaviorSpec,
    constantInitializer: Option[String],
    invariants: List[String],
    temporalProperties: List[String],
    tlcConfig: Option[TlcConfigInput],
    view: Option[String],
    persistent: List[String])

/** A trace source and the expressions evaluated in each state. */
final case class TraceEvaluationOptions(
    trace: InputSource,
    expressions: List[String])

/** Resolved server port and implementation. */
final case class ServerOptions(
    port: Int,
    serverType: ServerType)

/** Complete validated options for parsing a specification. */
final case class ResolvedParseOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path])

/** Complete validated options for parsing and typechecking a specification. */
final case class ResolvedTypecheckOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path],
    typechecker: TypecheckerOptions)

/** Complete validated options for model checking a specification. */
final case class ResolvedCheckOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path],
    typechecker: TypecheckerOptions,
    checker: CheckerOptions,
    specification: SpecificationOptions)

/** Complete validated options for evaluating expressions over a trace. */
final case class ResolvedTraceOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path],
    typechecker: TypecheckerOptions,
    checker: CheckerOptions,
    specification: SpecificationOptions,
    traceEvaluation: TraceEvaluationOptions) {

  def withLength(length: Int): ResolvedTraceOptions =
    copy(checker = checker.copy(length = length))
}

/** Complete validated options for starting a server. */
final case class ResolvedServerOptions(
    common: CommonOptions,
    server: ServerOptions)

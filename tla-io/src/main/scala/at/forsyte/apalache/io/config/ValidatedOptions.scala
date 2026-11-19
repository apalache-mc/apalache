package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.tlc.config.{BehaviorSpec, TlcConfig}
import at.forsyte.apalache.tla.lir.Feature

import java.nio.file.Path

/**
 * Configuration options that have passed validation. Implementations of `ValidatedOptions` are consumed by Apalache
 * passes.
 */
sealed trait ValidatedOptions

/** Validated settings shared by every execution mode. */
final case class CommonOptions(
    debug: Boolean,
    features: List[Feature],
    outDir: Path,
    profiling: Boolean,
    runDir: Option[Path],
    smtprof: Boolean,
    writeIntermediate: Boolean)
    extends ValidatedOptions

/** Values needed to initialize output and logging for a command. */
final case class CommandInitializationOptions(
    command: String,
    common: CommonOptions,
    source: Option[InputSource])
    extends ValidatedOptions

/** Input and output values injected into the frontend passes. */
final case class ModuleIoOptions(
    source: InputSource,
    output: Option[Path])
    extends ValidatedOptions

/** Validated type-inference settings. */
final case class TypecheckerOptions(inferPoly: Boolean) extends ValidatedOptions

/** Validated model-checker engine settings independent of the specification. */
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
    extends ValidatedOptions

/** A parsed TLC configuration together with its source path. */
final case class TlcConfigInput(
    config: TlcConfig,
    path: Path)
    extends ValidatedOptions

/** Validated behavior, properties, and TLC-derived specification settings. */
final case class SpecificationOptions(
    behaviorSpec: BehaviorSpec,
    constantInitializer: Option[String],
    invariants: List[String],
    temporalProperties: List[String],
    tlcConfig: Option[TlcConfigInput],
    view: Option[String],
    persistent: List[String])
    extends ValidatedOptions

/** A trace source and the expressions evaluated in each state. */
final case class TraceEvaluationOptions(
    trace: InputSource,
    expressions: List[String])
    extends ValidatedOptions

/** Validated server endpoint and implementation. The IP address is defined only for the explorer server. */
final case class ServerOptions(
    ip: Option[String],
    port: Int,
    serverType: ServerType)
    extends ValidatedOptions

/** Complete validated options for parsing a specification. */
final case class ValidatedParseOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path])
    extends ValidatedOptions

/** Complete validated options for parsing and typechecking a specification. */
final case class ValidatedTypecheckOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path],
    typechecker: TypecheckerOptions)
    extends ValidatedOptions

/** Complete validated options for model checking a specification. */
final case class ValidatedCheckOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path],
    typechecker: TypecheckerOptions,
    checker: CheckerOptions,
    specification: SpecificationOptions)
    extends ValidatedOptions

/** Complete validated options for evaluating expressions over a trace. */
final case class ValidatedTraceOptions(
    common: CommonOptions,
    source: InputSource,
    output: Option[Path],
    typechecker: TypecheckerOptions,
    checker: CheckerOptions,
    specification: SpecificationOptions,
    traceEvaluation: TraceEvaluationOptions)
    extends ValidatedOptions {

  def withLength(length: Int): ValidatedTraceOptions =
    copy(checker = checker.copy(length = length))
}

/** Complete validated options for starting a server. */
final case class ValidatedServerOptions(
    common: CommonOptions,
    server: ServerOptions)
    extends ValidatedOptions

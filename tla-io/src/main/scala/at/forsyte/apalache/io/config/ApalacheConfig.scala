package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource

import java.nio.file.Path

/**
 * Top-level sparse configuration assembled from scalar values and section patches. This configuration is used as the
 * input for producing command-specific options with [[ApalacheConfigResolver]].
 */
final case class ApalacheConfig(
    context: RunContextPatch = RunContextPatch(),
    common: CommonPatch = CommonPatch(),
    source: Option[InputSource] = None,
    output: Option[Path] = None,
    checker: CheckerPatch = CheckerPatch(),
    typechecker: TypecheckerPatch = TypecheckerPatch(),
    traceEvaluation: TraceEvaluationPatch = TraceEvaluationPatch(),
    server: ServerPatch = ServerPatch()) {

  def withCommand(command: String): ApalacheConfig =
    copy(context = context.copy(command = Some(command)))

  /** Merge this higher-precedence configuration with `lower`, which supplies only missing values. */
  def mergeWithLower(lower: ApalacheConfig): ApalacheConfig = {
    // Avoid reflection: explicit fields keep missing-field updates and exceptional merge rules visible.
    ApalacheConfig(
        context = ApalacheConfig.mergeContext(context, lower.context),
        common = ApalacheConfig.mergeCommon(common, lower.common),
        source = source.orElse(lower.source),
        output = output.orElse(lower.output),
        checker = ApalacheConfig.mergeChecker(checker, lower.checker),
        typechecker = ApalacheConfig.mergeTypechecker(typechecker, lower.typechecker),
        traceEvaluation = ApalacheConfig.mergeTraceEvaluation(traceEvaluation, lower.traceEvaluation),
        server = ApalacheConfig.mergeServer(server, lower.server),
    )
  }

  /** Fill absent fields with static built-in values. Context-dependent defaults are resolved later. */
  def mergeWithDefaults: ApalacheConfig =
    mergeWithLower(ApalacheConfig.defaults)
}

object ApalacheConfig {
  val empty: ApalacheConfig = ApalacheConfig()

  /** Static built-in values shared by resolution, diagnostics, and user-facing descriptions. */
  val defaults: ApalacheConfig = ApalacheConfig(
      common = CommonPatch(
          outDir = Some(Path.of(System.getProperty("user.dir"), "_apalache-out")),
          debug = Some(false),
          smtprof = Some(false),
          writeIntermediate = Some(false),
          profiling = Some(false),
          features = Some(Nil),
      ),
      checker = CheckerPatch(
          tuning = Some(Map.empty),
          algorithm = Some(Algorithm.Incremental),
          searchKind = Some(SearchKind.Check),
          outputTraces = Some(false),
          discardDisabled = Some(true),
          length = Some(10),
          maxError = Some(1),
          timeoutSmtSeconds = Some(0),
          smtSolver = Some(SMTSolver.Z3),
          smtEncoding = Some(SMTEncoding.OOPSLA19),
      ),
      typechecker = TypecheckerPatch(Some(true)),
      server = ServerPatch(
          port = Some(8822),
          serverType = Some(ServerType.Checker),
      ),
  )

  private def mergeContext(higher: RunContextPatch, lower: RunContextPatch): RunContextPatch =
    RunContextPatch(
        command = higher.command.orElse(lower.command),
        configFile = higher.configFile.orElse(lower.configFile),
    )

  private def mergeCommon(higher: CommonPatch, lower: CommonPatch): CommonPatch =
    CommonPatch(
        outDir = higher.outDir.orElse(lower.outDir),
        runDir = higher.runDir.orElse(lower.runDir),
        debug = higher.debug.orElse(lower.debug),
        smtprof = higher.smtprof.orElse(lower.smtprof),
        writeIntermediate = higher.writeIntermediate.orElse(lower.writeIntermediate),
        profiling = higher.profiling.orElse(lower.profiling),
        features = higher.features.orElse(lower.features),
    )

  private def mergeChecker(higher: CheckerPatch, lower: CheckerPatch): CheckerPatch =
    CheckerPatch(
        tuning = mergeMaps(higher.tuning, lower.tuning),
        algorithm = higher.algorithm.orElse(lower.algorithm),
        searchKind = higher.searchKind.orElse(lower.searchKind),
        seed = higher.seed.orElse(lower.seed),
        maxRun = higher.maxRun.orElse(lower.maxRun),
        outputTraces = higher.outputTraces.orElse(lower.outputTraces),
        tlcConfig = higher.tlcConfig.orElse(lower.tlcConfig),
        discardDisabled = higher.discardDisabled.orElse(lower.discardDisabled),
        constantInitializer = higher.constantInitializer.orElse(lower.constantInitializer),
        init = higher.init.orElse(lower.init),
        invariants = higher.invariants.orElse(lower.invariants),
        next = higher.next.orElse(lower.next),
        length = higher.length.orElse(lower.length),
        maxError = higher.maxError.orElse(lower.maxError),
        timeoutSmtSeconds = higher.timeoutSmtSeconds.orElse(lower.timeoutSmtSeconds),
        checkDeadlocks = higher.checkDeadlocks.orElse(lower.checkDeadlocks),
        smtSolver = higher.smtSolver.orElse(lower.smtSolver),
        smtEncoding = higher.smtEncoding.orElse(lower.smtEncoding),
        temporalProperties = higher.temporalProperties.orElse(lower.temporalProperties),
        view = higher.view.orElse(lower.view),
    )

  private def mergeTypechecker(higher: TypecheckerPatch, lower: TypecheckerPatch): TypecheckerPatch =
    TypecheckerPatch(higher.inferPoly.orElse(lower.inferPoly))

  private def mergeTraceEvaluation(
      higher: TraceEvaluationPatch,
      lower: TraceEvaluationPatch): TraceEvaluationPatch =
    TraceEvaluationPatch(
        trace = higher.trace.orElse(lower.trace),
        expressions = higher.expressions.orElse(lower.expressions),
    )

  private def mergeServer(higher: ServerPatch, lower: ServerPatch): ServerPatch =
    ServerPatch(
        port = higher.port.orElse(lower.port),
        serverType = higher.serverType.orElse(lower.serverType),
    )

  private def mergeMaps(
      higher: Option[Map[String, String]],
      lower: Option[Map[String, String]]): Option[Map[String, String]] =
    (higher, lower) match {
      case (None, _)               => lower
      case (_, None)               => higher
      case (Some(high), Some(low)) => Some(low ++ high)
    }
}

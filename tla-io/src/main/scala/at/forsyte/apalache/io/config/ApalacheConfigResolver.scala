package at.forsyte.apalache.io.config

import at.forsyte.apalache.infra.tlc.TlcConfigParserApalache
import at.forsyte.apalache.infra.tlc.config.{BehaviorSpec, InitNextSpec, TlcConfig, TlcConfigParseError}
import at.forsyte.apalache.io.InputSource
import org.slf4j.LoggerFactory

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.collection.mutable.ListBuffer

/** Applies defaults, loads TLC configuration, validates a mode, and constructs its final options. */
object ApalacheConfigResolver {

  import Constants._

  private val logger = LoggerFactory.getLogger(getClass)

  /** Behavior operator used when neither application nor TLC configuration supplies one. */
  val defaultInit: String = "Init"

  /** Transition operator used when neither application nor TLC configuration supplies one. */
  val defaultNext: String = "Next"

  /** Deadlock setting used when neither application nor TLC configuration supplies one. */
  val defaultCheckDeadlocks: Boolean = true

  /** Resolve the values needed to initialize output and logging for a command. */
  def resolveCommandInitialization(config: ApalacheConfig): ConfigParseResult[CommandInitializationOptions] = {
    val commandResult = requireCommand(config)
    if (!commandResult.isSuccess) {
      ConfigParseResult.failureFrom(commandResult)
    } else {
      ConfigParseResult.success(
          CommandInitializationOptions(
              commandResult.requireValue(),
              resolveCommon(config),
              config.source,
          ),
          commandResult.warnings,
      )
    }
  }

  /** Resolve parsing options, requiring an input source and applying common defaults. */
  def resolveParse(config: ApalacheConfig): ConfigParseResult[ValidatedParseOptions] = {
    val commandResult = requireCommand(config)
    if (!commandResult.isSuccess) {
      ConfigParseResult.failureFrom(commandResult)
    } else {
      config.source match {
        case None =>
          ConfigParseResult.failure(
              List(s"Missing value for required option $SOURCE"),
              commandResult.warnings,
          )
        case Some(source) =>
          ConfigParseResult.success(
              ValidatedParseOptions(
                  resolveCommon(config),
                  source,
                  config.output,
              ),
              commandResult.warnings,
          )
      }
    }
  }

  /** Resolve typechecking options on top of the parsing options. */
  def resolveTypecheck(config: ApalacheConfig): ConfigParseResult[ValidatedTypecheckOptions] = {
    val parseResult = resolveParse(config)
    if (!parseResult.isSuccess) {
      ConfigParseResult.failureFrom(parseResult)
    } else {
      val parse = parseResult.requireValue()
      val typechecker = config.mergeWithDefaults.typechecker
      ConfigParseResult.success(
          ValidatedTypecheckOptions(
              parse.common,
              parse.source,
              parse.output,
              TypecheckerOptions(requireDefault(typechecker.inferPoly, s"$TYPECHECKER.$INFER_POLY")),
          ),
          parseResult.warnings,
      )
    }
  }

  /** Resolve checker options, including TLC configuration and cross-field validation. */
  def resolveCheck(config: ApalacheConfig): ConfigParseResult[ValidatedCheckOptions] = {
    val typecheckResult = resolveTypecheck(config)
    if (!typecheckResult.isSuccess) {
      return ConfigParseResult.failureFrom(typecheckResult)
    }

    val errors = ListBuffer.empty[String]
    val warnings = ListBuffer.from(typecheckResult.warnings)
    val configuredChecker = config.checker
    val checkerWithDefaults = config.mergeWithDefaults.checker
    val solver = requireDefault(checkerWithDefaults.smtSolver, s"$CHECKER.$SMT_SOLVER")
    val encoding = requireDefault(checkerWithDefaults.smtEncoding, s"$CHECKER.$SMT_ENCODING")
    val maxError = requireDefault(checkerWithDefaults.maxError, s"$CHECKER.$MAX_ERROR")

    if (solver == SMTSolver.CVC5 && encoding != SMTEncoding.OOPSLA19) {
      errors +=
        s"$CHECKER.$SMT_SOLVER=${SMTSolver.CVC5.name} currently supports only " +
          s"$CHECKER.$SMT_ENCODING=${SMTEncoding.OOPSLA19.name}, but got $encoding."
    }
    if (maxError > 1 && configuredChecker.view.isEmpty) {
      errors += s"Option $CHECKER.$MAX_ERROR=$maxError requires $CHECKER.$VIEW."
    }

    val specificationResult = resolveSpecification(configuredChecker)
    warnings ++= specificationResult.warnings
    if (!specificationResult.isSuccess) {
      errors ++= specificationResult.errors
    }

    if (errors.nonEmpty) {
      return ConfigParseResult.failure(errors.toList, warnings.toList)
    }

    val specification = specificationResult.requireValue()
    val checker = CheckerOptions(
        algorithm = requireDefault(checkerWithDefaults.algorithm, s"$CHECKER.$ALGO"),
        discardDisabled = requireDefault(checkerWithDefaults.discardDisabled, s"$CHECKER.$DISCARD_DISABLED"),
        length = requireDefault(checkerWithDefaults.length, s"$CHECKER.$LENGTH"),
        maxError = maxError,
        timeoutSmtSeconds = requireDefault(checkerWithDefaults.timeoutSmtSeconds, s"$CHECKER.$TIMEOUT_SMT"),
        checkDeadlocks = resolveDeadlockSetting(configuredChecker, specification, warnings),
        smtSolver = solver,
        smtEncoding = encoding,
        tuning = requireDefault(checkerWithDefaults.tuning, s"$CHECKER.$TUNING"),
    )
    val typecheck = typecheckResult.requireValue()
    ConfigParseResult.success(
        ValidatedCheckOptions(
            typecheck.common,
            typecheck.source,
            typecheck.output,
            typecheck.typechecker,
            checker,
            specification,
        ),
        warnings.toList,
    )
  }

  /** Resolve trace-evaluation options and validate the trace source and expressions. */
  def resolveTrace(config: ApalacheConfig): ConfigParseResult[ValidatedTraceOptions] = {
    val checkResult = resolveCheck(config)
    if (!checkResult.isSuccess) {
      return ConfigParseResult.failureFrom(checkResult)
    }

    val errors = ListBuffer.empty[String]
    config.traceEvaluation.trace match {
      case None =>
        errors += s"Missing value for required option $TRACEE.$TRACE"
      case Some(trace) =>
        trace.format match {
          case InputSource.Format.Itf | InputSource.Format.Json => ()
          case _ => errors += "Trace evaluation requires an ITF or JSON trace."
        }
    }
    if (config.traceEvaluation.expressions.forall(_.isEmpty)) {
      errors += s"Trace evaluation requires a nonempty list of $EXPRESSIONS."
    }

    if (errors.nonEmpty) {
      ConfigParseResult.failure(errors.toList, checkResult.warnings)
    } else {
      val check = checkResult.requireValue()
      ConfigParseResult.success(
          ValidatedTraceOptions(
              check.common,
              check.source,
              check.output,
              check.typechecker,
              check.checker,
              check.specification,
              TraceEvaluationOptions(
                  config.traceEvaluation.trace.get,
                  config.traceEvaluation.expressions.get,
              ),
          ),
          checkResult.warnings,
      )
    }
  }

  /** Resolve server options and apply the server defaults. */
  def resolveServer(config: ApalacheConfig): ConfigParseResult[ValidatedServerOptions] = {
    val commandResult = requireCommand(config)
    if (!commandResult.isSuccess) {
      ConfigParseResult.failureFrom(commandResult)
    } else {
      val server = config.mergeWithDefaults.server
      ConfigParseResult.success(
          ValidatedServerOptions(
              resolveCommon(config),
              ServerOptions(
                  port = requireDefault(server.port, s"$SERVER.$PORT"),
                  serverType = requireDefault(server.serverType, s"$SERVER.$SERVER_TYPE"),
              ),
          ),
          commandResult.warnings,
      )
    }
  }

  /** Resolve checker options for an exploration request whose source and predicates are supplied remotely. */
  def resolveRemote(
      base: ApalacheConfig,
      source: InputSource,
      init: String,
      next: String,
      invariants: List[String],
      persistent: List[String]): ConfigParseResult[ValidatedCheckOptions] = {

    val requestConfig = ApalacheConfig(
        context = RunContextPatch(command = Some(SERVER)),
        source = Some(source),
        checker = CheckerPatch(
            algorithm = Some(Algorithm.Remote),
            discardDisabled = Some(false),
            maxError = Some(1),
            timeoutSmtSeconds = Some(0),
            checkDeadlocks = Some(false),
            smtEncoding = Some(SMTEncoding.OOPSLA19),
            tuning = Some(Map.empty),
        ),
    )
    val remoteConfig = requestConfig.mergeWithLower(base)

    val resolved = resolveCheck(remoteConfig)
    if (!resolved.isSuccess) {
      ConfigParseResult.failureFrom(resolved)
    } else {
      val options = resolved.requireValue()
      ConfigParseResult.success(
          options.copy(specification = options.specification.copy(
              behaviorSpec = InitNextSpec(init, next),
              invariants = invariants,
              persistent = persistent,
          )),
          resolved.warnings,
      )
    }
  }

  private def requireCommand(config: ApalacheConfig): ConfigParseResult[String] =
    config.context.command match {
      case Some(command) => ConfigParseResult.success(command)
      case None          => ConfigParseResult.failure(s"Missing value for required option $COMMAND")
    }

  private def resolveCommon(config: ApalacheConfig): CommonOptions = {
    val common = config.mergeWithDefaults.common
    CommonOptions(
        debug = requireDefault(common.debug, DEBUG),
        features = requireDefault(common.features, FEATURES),
        outDir = requireDefault(common.outDir, OUT_DIR),
        profiling = requireDefault(common.profiling, PROFILING),
        runDir = common.runDir,
        smtprof = requireDefault(common.smtprof, SMTPROF),
        writeIntermediate = requireDefault(common.writeIntermediate, WRITE_INTERMEDIATE),
    )
  }

  /** Return a static default after [[ApalacheConfig.mergeWithDefaults]] has supplied it. */
  private def requireDefault[A](value: Option[A], field: String): A =
    value.getOrElse(throw new IllegalStateException(s"Missing built-in default for $field"))

  private def resolveSpecification(checker: CheckerPatch): ConfigParseResult[SpecificationOptions] = {
    if (checker.tlcConfig.isEmpty) {
      return ConfigParseResult.success(SpecificationOptions(
              behaviorSpec = InitNextSpec(checker.init.getOrElse(defaultInit), checker.next.getOrElse(defaultNext)),
              constantInitializer = checker.constantInitializer,
              invariants = checker.invariants.getOrElse(Nil),
              temporalProperties = checker.temporalProperties.getOrElse(Nil),
              tlcConfig = None,
              view = checker.view,
              persistent = Nil,
          ))
    }

    val path = checker.tlcConfig.get
    val loaded = loadTlcConfig(path)
    if (!loaded.isSuccess) {
      return ConfigParseResult.failureFrom(loaded)
    }

    val tlc = loaded.requireValue()
    val warnings = ListBuffer.empty[String]
    val behavior: BehaviorSpec = tlc.behaviorSpec match {
      case InitNextSpec(tlcInit, tlcNext) =>
        val init = overrideString(checker.init, tlcInit, s"$CHECKER.$INIT", warnings)
        val next = overrideString(checker.next, tlcNext, s"$CHECKER.$NEXT", warnings)
        InitNextSpec(init, next)
      case other => other
    }
    val invariants = overrideList(checker.invariants, tlc.invariants, s"$CHECKER.$INV", warnings)
    val temporal =
      overrideList(checker.temporalProperties, tlc.temporalProps, s"$CHECKER.$TEMPORAL", warnings)

    ConfigParseResult.success(
        SpecificationOptions(
            behaviorSpec = behavior,
            constantInitializer = checker.constantInitializer,
            invariants = invariants,
            temporalProperties = temporal,
            tlcConfig = Some(TlcConfigInput(tlc, path)),
            view = checker.view,
            persistent = Nil,
        ),
        warnings.toList,
    )
  }

  private def loadTlcConfig(path: Path): ConfigParseResult[TlcConfig] = {
    if (!Files.exists(path)) {
      return ConfigParseResult.failure(s"Specified TLC config file not found: ${path.toAbsolutePath}")
    }

    logger.info(s"  > ${path.getFileName}: Loading TLC configuration")

    val reader =
      try Files.newBufferedReader(path, StandardCharsets.UTF_8)
      catch {
        case e: java.io.IOException =>
          return ConfigParseResult.failure(
              s"${path.getFileName}: IO error when loading the TLC config: ${e.getMessage}")
      }

    try {
      ConfigParseResult.success(TlcConfigParserApalache(reader))
    } catch {
      case e: java.io.IOException =>
        ConfigParseResult.failure(s"${path.getFileName}: IO error when loading the TLC config: ${e.getMessage}")
      case e: TlcConfigParseError =>
        ConfigParseResult.failure(s"${path.getFileName}:${e.pos}: Error parsing the TLC config file: ${e.msg}")
    } finally {
      reader.close()
    }
  }

  private def resolveDeadlockSetting(
      checker: CheckerPatch,
      specification: SpecificationOptions,
      warnings: ListBuffer[String]): Boolean = {
    val tlcValue = specification.tlcConfig.flatMap(_.config.checkDeadlock)

    tlcValue match {
      case Some(value) if checker.checkDeadlocks.nonEmpty =>
        val configured = checker.checkDeadlocks.get
        if (configured != value) {
          warnings +=
            s"TLC CHECK_DEADLOCK=$value is overridden by $CHECKER.$NO_DEADLOCK=${!configured}."
        }
        configured
      case Some(value) =>
        warnings += s"Using CHECK_DEADLOCK=$value from the TLC configuration."
        value
      case None =>
        checker.checkDeadlocks.getOrElse(defaultCheckDeadlocks)
    }
  }

  private def overrideString(
      configured: Option[String],
      fromTlc: String,
      field: String,
      warnings: ListBuffer[String]): String =
    configured match {
      case Some(value) =>
        if (fromTlc.nonEmpty) warnings += s"$field overrides the value from the TLC configuration."
        value
      case None =>
        if (fromTlc.nonEmpty) {
          logger.info(s"  > Using ${displayName(field)} predicate(s) $fromTlc from the TLC config")
        }
        fromTlc
    }

  private def overrideList(
      configured: Option[List[String]],
      fromTlc: List[String],
      field: String,
      warnings: ListBuffer[String]): List[String] =
    configured match {
      case Some(values) =>
        if (fromTlc.nonEmpty) warnings += s"$field overrides the value from the TLC configuration."
        values
      case None =>
        if (fromTlc.nonEmpty) {
          logger.info(s"  > Using ${displayName(field)} predicate(s) ${fromTlc.mkString(", ")} from the TLC config")
        }
        fromTlc
    }

  private def displayName(field: String): String =
    field.stripPrefix(s"$CHECKER.")
}

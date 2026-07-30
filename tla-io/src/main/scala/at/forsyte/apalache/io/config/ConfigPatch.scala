package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.tla.lir.Feature

import java.nio.file.Path

/**
 * A section of [[ApalacheConfig]] that can be merged into a configuration file.
 * Patches are introduced as logical configuration pieces that are required
 * by Apalache commands.
 */
sealed trait ConfigPatch

/** Patches the top-level `command` and `config-file` execution metadata. */
final case class RunContextPatch(
    command: Option[String] = None,
    configFile: Option[Path] = None)
    extends ConfigPatch

/** Patches top-level output, logging, profiling, and feature settings. */
final case class CommonPatch(
    outDir: Option[Path] = None,
    runDir: Option[Path] = None,
    debug: Option[Boolean] = None,
    smtprof: Option[Boolean] = None,
    writeIntermediate: Option[Boolean] = None,
    profiling: Option[Boolean] = None,
    features: Option[List[Feature]] = None)
    extends ConfigPatch

/** Patches model-checking behavior in `checker`. */
final case class CheckerPatch(
    tuning: Option[Map[String, String]] = None,
    algorithm: Option[Algorithm] = None,
    tlcConfig: Option[Path] = None,
    discardDisabled: Option[Boolean] = None,
    constantInitializer: Option[String] = None,
    init: Option[String] = None,
    invariants: Option[List[String]] = None,
    next: Option[String] = None,
    length: Option[Int] = None,
    maxError: Option[Int] = None,
    timeoutSmtSeconds: Option[Int] = None,
    checkDeadlocks: Option[Boolean] = None,
    smtSolver: Option[SMTSolver] = None,
    smtEncoding: Option[SMTEncoding] = None,
    temporalProperties: Option[List[String]] = None,
    view: Option[String] = None)
    extends ConfigPatch

/** Patches type-inference behavior in `typechecker`. */
final case class TypecheckerPatch(inferPoly: Option[Boolean] = None) extends ConfigPatch

/** Patches the trace input and evaluated expressions in `tracee`. */
final case class TraceEvaluationPatch(
    trace: Option[InputSource] = None,
    expressions: Option[List[String]] = None)
    extends ConfigPatch

/** Patches the listening port and server implementation in `server`. */
final case class ServerPatch(
    port: Option[Int] = None,
    serverType: Option[ServerType] = None)
    extends ConfigPatch

package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource

import scala.collection.mutable.ListBuffer

/** Validates untrusted service configuration without consulting the filesystem. */
object RemoteConfigValidator {

  /** Tuning keys that can cause Z3 to create caller-selected or implicit files. */
  val FileWritingTuningKeys: Set[String] = Set(
      "z3.dot_proof_file",
      "z3.trace",
      "z3.trace_file_name",
      "z3.sat.drat.file",
      "z3.sat.inprocess.out",
      "z3.solver.axioms2files",
      "z3.solver.cancel_backup_file",
      "z3.solver.proof.log",
      "z3.solver.smtlib2_log",
      "z3.opt.dump_benchmarks",
      "z3.opt.solution_prefix",
      "z3.smt.arith.dump_lemmas",
  )

  /** Parse and validate one remote request configuration without loading configuration files. */
  def parse(
      sourceText: String,
      sourceName: String = "<RPC configuration>"): ConfigParseResult[ApalacheConfig] = {
    val parsed = ApalacheConfigJsonParser.parse(sourceText, sourceName)
    if (!parsed.isSuccess) {
      ConfigParseResult.failureFrom(parsed)
    } else {
      ConfigParseResult.withWarnings(validate(parsed.requireValue()), parsed.warnings)
    }
  }

  /** Reject all request-controlled paths and solver settings capable of writing files. */
  def validate(config: ApalacheConfig): ConfigParseResult[ApalacheConfig] = {
    val errors = ListBuffer.empty[String]

    rejectPath(config.context.configFile.nonEmpty, "$.config-file", errors)
    rejectPath(config.common.outDir.nonEmpty, "$.out-dir", errors)
    rejectPath(config.common.runDir.nonEmpty, "$.run-dir", errors)
    rejectPath(config.output.nonEmpty, "$.output", errors)
    rejectPath(config.checker.tlcConfig.nonEmpty, "$.checker.config", errors)

    config.source match {
      case Some(_: InputSource.FileSource) => rejectFileSource("$.source", errors)
      case _                               => ()
    }
    config.traceEvaluation.trace match {
      case Some(_: InputSource.FileSource) => rejectFileSource("$.tracee.trace", errors)
      case _                               => ()
    }

    config.checker.tuning
      .getOrElse(Map.empty)
      .keySet
      .intersect(FileWritingTuningKeys)
      .toSeq
      .sorted
      .foreach { key =>
        errors += s"$$.checker.tuning.$key: This tuning option can write files and is not allowed in remote configuration."
      }

    if (errors.isEmpty) ConfigParseResult.success(config)
    else ConfigParseResult.failure(errors.toList)
  }

  private def rejectPath(present: Boolean, path: String, errors: ListBuffer[String]): Unit =
    if (present) {
      errors += s"$path: Filesystem paths are not allowed in remote configuration."
    }

  private def rejectFileSource(path: String, errors: ListBuffer[String]): Unit =
    errors += s"$path: File-backed sources are not allowed in remote configuration; provide in-memory content."
}

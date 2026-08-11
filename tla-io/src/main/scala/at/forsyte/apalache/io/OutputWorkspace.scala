package at.forsyte.apalache.io

import java.io.PrintWriter
import java.nio.file.Path

/**
 * Owns the output workspace for one Apalache execution. See <a
 * href="https://github.com/apalache-mc/apalache/blob/main/docs/src/adr/009adr-outputs.md">ADR-009</a> for the output
 * layout.
 */
trait OutputWorkspace {
  def runDir: Path
  def additionalRunDir: Option[Path]
  def openWriter(path: Path): PrintWriter
  def withWriter(path: Path)(f: PrintWriter => Unit): Unit
  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit
  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit
  def withProfilingWriter(f: PrintWriter => Unit): Boolean
}

/** Names shared by output producers. */
object OutputWorkspace {

  /** Name of the subdirectory that stores intermediate representations produced during a run. */
  private[io] val IntermediateDirName = "intermediate"

  /** Name of the file in the run directory that records the command invocation. */
  val RunFile = "run.txt"

  /** Name of the debug snapshot containing the merged application configuration. */
  val ConfigFile = "config.json"

  /** Name of the generated bug-report template. */
  val ReportFile = "BugReport.md"

  /** Name of the detailed application log. */
  val DetailedLogFile = "detailed.log"

  /** Name of the general rule-profiling report. */
  val RuleProfileFile = "profile-rules.txt"

  /** Name of the SMT constraint-profiling report. */
  val SmtProfileFile = "profile.csv"

  /** Return the detailed application log inside `runDir`. */
  def detailedLogPath(runDir: Path): Path = runDir.resolve(DetailedLogFile)

  /** Return the general rule-profiling report inside `runDir`. */
  def ruleProfilePath(runDir: Path): Path = runDir.resolve(RuleProfileFile)

  /** Return the SMT constraint-profiling report inside `runDir`. */
  def smtProfilePath(runDir: Path): Path = runDir.resolve(SmtProfileFile)
}

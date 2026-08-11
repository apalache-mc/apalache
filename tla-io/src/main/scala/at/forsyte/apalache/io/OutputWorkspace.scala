package at.forsyte.apalache.io

import java.io.PrintWriter
import java.nio.file.Path

/**
 * Owns the output locations and writer lifecycle conventions for one Apalache execution.
 *
 * Run-directory output may be mirrored to an additional directory. See <a
 * href="https://github.com/apalache-mc/apalache/blob/main/docs/src/adr/009adr-outputs.md">ADR-009</a> for the output
 * layout.
 */
trait OutputWorkspace {

  /**
   * Resolve `parts` relative to the primary run directory.
   *
   * @param parts
   *   path components relative to the primary run directory
   * @return
   *   the resolved path
   */
  def pathInRunDir(parts: String*): Path

  /**
   * Open a writer for `fileName` in the primary run directory and, when configured, another in the additional run
   * directory.
   *
   * These writers are intended for output that remains open throughout a long-running operation. The caller owns the
   * returned writers and must close each of them.
   *
   * @param fileName
   *   the file name relative to each run directory
   * @return
   *   the opened writers, with the primary run-directory writer first
   */
  def openLongLivedWritersInRunDirs(fileName: String): Iterable[PrintWriter]

  /**
   * Apply `f` to a writer below the primary run directory and repeat the operation below the additional run directory
   * when configured.
   *
   * @param parts
   *   path components relative to each run directory; all parent directories must already exist
   * @param f
   *   the operation to perform with each writer
   */
  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit

  /**
   * When intermediate output is enabled, apply `f` to a writer below each configured intermediate-output directory.
   *
   * @param parts
   *   path components relative to each intermediate-output directory; all parent directories must already exist
   * @param f
   *   the operation to perform with each writer
   */
  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit

  /**
   * Apply `f` to the rule-profiling output writer in each run directory when profiling is enabled.
   *
   * @param f
   *   the operation that writes the profiling output
   * @return
   *   `true` when profiling is enabled and the operation was applied, or `false` otherwise
   */
  def withProfilingWriter(f: PrintWriter => Unit): Boolean

  /**
   * Apply `f` to a writer for `path` and close the writer afterward.
   *
   * <b>Note:</b> `path` is not restricted to the directories owned by this workspace!
   * Use this method only in the rare cases when you have to write to an arbitrary path.
   * For example, `parse --output=filename` is a rare case when it's needed.
   *
   * @param path
   *   the file to write
   * @param f
   *   the operation to perform with the writer
   */
  def withWriterOutsideWorkspace(path: Path)(f: PrintWriter => Unit): Unit
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

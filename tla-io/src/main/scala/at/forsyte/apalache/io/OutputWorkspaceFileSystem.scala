package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.CommandInitializationOptions

import java.io.IOException
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

/**
 * A filesystem-backed output workspace for one Apalache execution. It creates all configured directories during
 * construction and mirrors run output to an additional run directory when requested.
 *
 * @param initialization
 *   resolved values that determine this execution's output locations and enabled output features
 *
 * @author
 *   Jure Kukovec, Shon Feder, Igor Konnov
 */
final class OutputWorkspaceFileSystem(initialization: CommandInitializationOptions) extends OutputWorkspace {

  /** Namespace shared by all runs of the same input file or command. */
  private val outDir: Path = {
    val fileName = initialization.source match {
      case Some(InputSource.FileSource(path, _)) => path.getFileName.toString
      case _                                     => initialization.command
    }
    ensureDirExists(initialization.common.outDir.resolve(fileName).toAbsolutePath)
  }

  /** Unique persistent directory for this execution inside `outDir`. */
  override val runDir: Path = {
    val niceDate = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd"))
    val niceTime = LocalDateTime.now().format(DateTimeFormatter.ofPattern("HH-mm-ss"))
    // Despite the API name, this is a persistent run directory under outDir.
    // Note: createTempDirectory supplies a unique suffix so that concurrent executions do not collide.
    Files.createTempDirectory(outDir, s"${niceDate}T${niceTime}_")
  }

  /** User-selected additional directory to which run output is mirrored. */
  override val additionalRunDir: Option[Path] = initialization.common.runDir.map { path =>
    ensureDirExists(path.toAbsolutePath)
  }

  /** Intermediate-output directory inside `runDir`, present only when intermediate output is enabled. */
  private val intermediateDirOpt: Option[Path] =
    if (initialization.common.writeIntermediate) {
      Some(ensureDirExists(runDir.resolve(OutputWorkspace.IntermediateDirName)))
    } else {
      None
    }

  /** Intermediate-output directory inside the additional run directory, when both options are enabled. */
  private val additionalIntermediateRunDirOpt: Option[Path] =
    intermediateDirOpt.flatMap(_ =>
      additionalRunDir.map { path =>
        ensureDirExists(path.resolve(OutputWorkspace.IntermediateDirName))
      })

  /** Open a UTF-8 writer that the caller must close. Prefer [[withWriter]] for scoped writes. */
  override def openWriter(path: Path): PrintWriter = {
    new PrintWriter(Files.newBufferedWriter(path))
  }

  /** Apply `f` to a UTF-8 writer for `path`, then close the writer. */
  override def withWriter(path: Path)(f: PrintWriter => Unit): Unit = {
    val writer = openWriter(path)
    try {
      f(writer)
    } finally {
      writer.close()
    }
  }

  /** Write under the generated run directory and mirror the writer to the configured additional run directory. */
  override def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    withWriterInJointPath(runDir, parts, f)
    additionalRunDir.foreach(withWriterInJointPath(_, parts, f))
  }

  /** Write under each intermediate directory when intermediate output is enabled. */
  override def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    intermediateDirOpt.foreach { dir =>
      withWriterInJointPath(dir, parts, f)
      additionalIntermediateRunDirOpt.foreach(withWriterInJointPath(_, parts, f))
    }
  }

  /** Write the rule-profiling report when profiling is enabled; return whether a write occurred. */
  override def withProfilingWriter(f: PrintWriter => Unit): Boolean = {
    if (initialization.common.profiling) {
      withWriterInRunDir(OutputWorkspace.RuleProfileFile)(f)
      true
    } else {
      false
    }
  }

  /** Join `dir` and `parts`, and call `withWriter` with this path and `writeFun`. */
  private def withWriterInJointPath(dir: Path, parts: Seq[String], writeFun: PrintWriter => Unit): Unit = {
    val joinedPath = parts.foldLeft(dir)(_.resolve(_))
    withWriter(joinedPath)(writeFun)
  }

  private def ensureDirExists(path: Path): Path = {
    try {
      Files.createDirectories(path)
    } catch {
      case e: IOException =>
        throw new ConfigurationError(s"Could not find or create directory ${path.toAbsolutePath}: ${e.getMessage}")
    }
  }
}

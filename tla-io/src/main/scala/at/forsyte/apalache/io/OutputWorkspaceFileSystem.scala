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

  val runDir: Path = {
    val niceDate = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd"))
    val niceTime = LocalDateTime.now().format(DateTimeFormatter.ofPattern("HH-mm-ss"))
    // Despite the API name, this is a persistent run directory under outDir.
    // Note: createTempDirectory supplies a unique suffix so that concurrent executions do not collide.
    Files.createTempDirectory(outDir, s"${niceDate}T${niceTime}_")
  }

  val additionalRunDir: Option[Path] = initialization.common.runDir.map { path =>
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

  override def pathInRunDir(parts: String*): Path = {
    parts.foldLeft(runDir)(_.resolve(_))
  }

  override def openLongLivedWritersInRunDirs(fileName: String): Iterable[PrintWriter] = {
    (Some(runDir) ++ additionalRunDir).map { dir =>
      new PrintWriter(Files.newBufferedWriter(dir.resolve(fileName)))
    }
  }

  override def withWriter(path: Path)(f: PrintWriter => Unit): Unit = {
    val writer = new PrintWriter(Files.newBufferedWriter(path))
    try {
      f(writer)
    } finally {
      writer.close()
    }
  }

  override def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    withWriter(pathInRunDir(parts: _*))(f)
    additionalRunDir.foreach(withWriterInJointPath(_, parts, f))
  }

  override def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    intermediateDirOpt.foreach { dir =>
      withWriterInJointPath(dir, parts, f)
      additionalIntermediateRunDirOpt.foreach(withWriterInJointPath(_, parts, f))
    }
  }

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

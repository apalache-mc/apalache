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
 *   Jure Kukovec, Shon Feder, Igor Konnov, Thomas Pani
 */
final class OutputWorkspaceFileSystem(initialization: CommandInitializationOptions) extends OutputWorkspace {
  // helper function to create intermediate directories, if needed
  private def findOrCreateDir(path: Path): Path = {
    val absolutePath = path.toAbsolutePath
    try {
      Files.createDirectories(absolutePath)
    } catch {
      case e: IOException =>
        throw new ConfigurationError(s"Could not find or create directory $absolutePath: ${e.getMessage}")
    }
  }

  val runDir: Path = {
    // Namespace shared by all runs of the same input file or command (in the server mode).
    val groupName = initialization.source match {
      case Some(InputSource.FileSource(path, _)) => path.getFileName.toString
      case _                                     => initialization.command
    }
    // Create {outDir}/{filename or command} to group the runs by their source name.
    // Since the server mode does not have named sources, it uses the command name.
    // Note: Path.resolve works here because groupName is not an absolute name.
    val groupDirNameInOutDir = initialization.common.outDir.resolve(groupName)
    val groupDir = findOrCreateDir(groupDirNameInOutDir)
    // Create a unique directory under groupDir that looks like {yyyy-MM-dd}T{HH-mm-ss}_{suffix}
    val niceDate = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd"))
    val niceTime = LocalDateTime.now().format(DateTimeFormatter.ofPattern("HH-mm-ss"))
    // Despite the API name, this is a persistent run directory under outDir.
    // Note: createTempDirectory supplies a unique suffix so that concurrent executions do not collide.
    Files.createTempDirectory(groupDir, s"${niceDate}T${niceTime}_")
  }

  val additionalRunDir: Option[Path] = initialization.common.runDir.map { path =>
    findOrCreateDir(path)
  }

  /** Intermediate-output directory inside `runDir`, present only when intermediate output is enabled. */
  private val intermediateDirOpt: Option[Path] =
    if (initialization.common.writeIntermediate) {
      Some(findOrCreateDir(runDir.resolve(OutputWorkspace.IntermediateDirName)))
    } else {
      None
    }

  /** Intermediate-output directory inside the additional run directory, when both options are enabled. */
  private val additionalIntermediateDirOpt: Option[Path] =
    intermediateDirOpt.flatMap(_ =>
      additionalRunDir.map { path =>
        findOrCreateDir(path.resolve(OutputWorkspace.IntermediateDirName))
      })

  override def pathInRunDir(parts: String*): Path = {
    parts.foldLeft(runDir)(_.resolve(_))
  }

  override def openLongLivedWritersInRunDirs(fileName: String): Iterable[PrintWriter] = {
    (Some(runDir) ++ additionalRunDir).map { dir =>
      new PrintWriter(Files.newBufferedWriter(dir.resolve(fileName)))
    }
  }

  override def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    withWriterInternal(pathInRunDir(parts: _*))(f)
    additionalRunDir.foreach(withWriterInJointPath(_, parts, f))
  }

  override def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    intermediateDirOpt.foreach { dir =>
      withWriterInJointPath(dir, parts, f)
      additionalIntermediateDirOpt.foreach(withWriterInJointPath(_, parts, f))
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

  override def withWriterOutsideWorkspace(path: Path)(f: PrintWriter => Unit): Unit = {
    withWriterInternal(path)(f)
  }

  // an internal implementation of withWriter
  private def withWriterInternal(path: Path)(f: PrintWriter => Unit): Unit = {
    val writer = new PrintWriter(Files.newBufferedWriter(path))
    try {
      f(writer)
    } finally {
      writer.close()
    }
  }

  /** Join `dir` and `parts`, and call `withWriterOutsideWorkspace` with this path and `writeFun`. */
  private def withWriterInJointPath(dir: Path, parts: Seq[String], writeFun: PrintWriter => Unit): Unit = {
    val joinedPath = parts.foldLeft(dir)(_.resolve(_))
    withWriterInternal(joinedPath)(writeFun)
  }
}

package at.forsyte.apalache.io

import java.io.OutputStream
import java.io.PrintWriter
import java.nio.file.Path

/** A filesystem-free output workspace for tests that do not inspect output files. */
object OutputWorkspaceNoopMock extends OutputWorkspace {

  override def pathInRunDir(parts: String*): Path = parts.foldLeft(Path.of("mock-output"))(_.resolve(_))

  override def openLongLivedWritersInRunDirs(fileName: String): Iterable[PrintWriter] =
    Iterable(new PrintWriter(OutputStream.nullOutputStream()))

  override def withWriter(path: Path)(f: PrintWriter => Unit): Unit = withNullWriter(f)

  override def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit = withNullWriter(f)

  override def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit = ()

  override def withProfilingWriter(f: PrintWriter => Unit): Boolean = false

  private def withNullWriter(f: PrintWriter => Unit): Unit = {
    val writer = new PrintWriter(OutputStream.nullOutputStream())
    try {
      f(writer)
    } finally {
      writer.close()
    }
  }
}

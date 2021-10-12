package at.forsyte.apalache.io

import at.forsyte.apalache.infra.passes.PassOptions

import java.io.File
import java.nio.file.{Files, InvalidPathException, Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import scala.io.Source

/**
 * The OutputManager is the central source of truth, for all IO related locations.
 * Any IO operation should request read/write target paths from this object.
 */
object OutputManager {

  object Names {
    val OUTDIR = "OUTDIR"
    val INTERMEDIATE_FLAG = "write-intermediate"
    val INTERMEDIATE_FOLDERNAME = "intermediate"
    val PROFILING_FLAG = "profiling"
    val CFG_FILE = ".tlaplus/apalache.cfg"
  }

  import Names._
  // Absolute path
  private var OUTPUT_DIR: String = ""
  private var runDirOpt: Option[Path] = None
  private var flags: Map[String, Boolean] =
    Map(
        INTERMEDIATE_FLAG -> false,
        PROFILING_FLAG -> false
    )

  def isConfigured: Boolean = outDirAsFile.isDirectory && runDirOpt.nonEmpty

  def outDirAsFile: File = new File(OUTPUT_DIR)
  def runDirPathUnsafe: Path = runDirOpt.get

  def inRunDir[T](cmd: Path => T): T = cmd(runDirPathUnsafe)

  def syncFromCFG(): Unit = {
    val flagRegex = raw"^([a-zA-Z\-]+)\s*=\s*(.+)\s*$$".r
    val home = System.getProperty("user.home")
    val configFile = new File(home, CFG_FILE)
    if (configFile.exists()) {
      val src = Source.fromFile(configFile.getAbsolutePath)
      var updated = Set.empty[String]
      for (line <- src.getLines) {
        flagRegex.findAllMatchIn(line.strip()).foreach { m =>
          val flagname = m.group(1)
          val flagVal = m.group(2)
          if (flagname == OUTDIR) {
            val replacedHome =
              if (flagVal.startsWith("~")) flagVal.replaceFirst("~", home)
              else flagVal
            val outdir = new File(replacedHome)
            if (!outdir.exists()) {
              outdir.mkdir()
            }
            if (!outdir.exists()) {
              // Throw or log failure and ignore?
              //              throw new InvalidPathException(outdir.getCanonicalPath, "Invalid directory name or parent doesn't exist")
            } else {
              OUTPUT_DIR = outdir.getCanonicalPath
              updated += OUTDIR
            }
          } else if (flags.keySet.contains(flagname)) {
            flagVal match {
              case "TRUE" | "true" =>
                flags += flagname -> true
                updated += flagname
              case "FALSE" | "false" =>
                flags += flagname -> false
                updated += flagname
              case _ =>
              // Throw or log failure and ignore?
              //                throw new Exception(s"Flag $flagname must be one of: TRUE/true/FALSE/false.")
            }
          }
        }
      }
      src.close()
//      println(s"loaded the following from config: ${updated.mkString(", ")}")
    }
    if (OUTPUT_DIR.isEmpty)
      OUTPUT_DIR = System.getProperty("user.dir")
  }

  def syncFromOptions(opt: PassOptions): Unit = {
    opt.get[Boolean]("general", INTERMEDIATE_FLAG) foreach {
      flags += INTERMEDIATE_FLAG -> _
    }
    opt.get[Boolean]("general", PROFILING_FLAG) foreach {
      flags += PROFILING_FLAG -> _
    }
  }

  /** lends flags to execute `cmd` conditionally */
  def doIfFlag(flagName: String)(cmd: => Unit): Unit =
    flags
      .get(flagName)
      .foreach(flag =>
        if (flag) {
          cmd
        }
      )

  def createRunDirectory(specName: String): Unit =
    if (runDirOpt.isEmpty) {
      val nicetime = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"yyyy-MM-dd_HH-mm-ss_"))
      val outdir = outDirAsFile
      if (!outdir.exists()) {
        outdir.mkdir()
      }
      // suffix for parallel runs
      val rundir = Files.createTempDirectory(Paths.get(outdir.getAbsolutePath), s"${specName}_" + nicetime)
      runDirOpt = Some(rundir)
    }

  def createIntermediateFolder(runDir: Path): Option[File] = {
    if (flags("write-intermediate")) {
      val ceDir = new File(runDir.toFile.getAbsolutePath, "intermediate")
      if (!ceDir.exists()) {
        ceDir.mkdir()
      }
      Some(ceDir)
    } else None
  }
}

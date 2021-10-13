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
    val OUTDIR_NAME_IN_CFG = "OUTDIR"
    val INTERMEDIATE_FLAG = "write-intermediate"
    val INTERMEDIATE_FOLDERNAME = "intermediate"
    val PROFILING_FLAG = "profiling"
    val CFG_FILE = ".tlaplus/apalache.cfg"
    val DEFAULT_OUTDIR = "x"
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

  /** If this is FALSE, outputs (of any sort) cannot happen, so the tool should exit */
  def isConfigured: Boolean = outDirAsFile.isDirectory && runDirOpt.nonEmpty

  /** Accessors */
  def outDirAsFile: File = new File(OUTPUT_DIR)
  def runDirPathUnsafe: Path = runDirOpt.get /* Should throw if called before `createRunDir` */

  /** Executes a command in the run directory. To be used by classes attempting to write output files */
  def inRunDir(cmd: Path => Unit): Unit = runDirOpt.foreach { cmd }

  /** Executes a command in the run directory. To be used by classes attempting to write output files */
  def withRunDir[T](default: T)(cmd: Path => T): T = runDirOpt.map(cmd).getOrElse(default)

  /** Loads the Apalache configuration file from HOME/.tlaplus */
  def syncFromCFG(): Unit = {
    val flagRegex = raw"^\s*([a-zA-Z\-]+)\s*=\s*(.+)\s*$$".r
    val home = System.getProperty("user.home")
    val configFile = new File(home, CFG_FILE)
    if (configFile.exists()) {
      val src = Source.fromFile(configFile.getAbsolutePath)
      for (line <- src.getLines) {
        flagRegex.findAllMatchIn(line).foreach { m =>
          // Flags have the shape FLAGNAME=FLAGVAL
          val flagname = m.group(1)
          val flagVal = m.group(2)
          if (flagname == OUTDIR_NAME_IN_CFG) {
            // OUTDIR is a special flag that governs the output directory
            val replacedHome =
              if (flagVal.startsWith("~")) flagVal.replaceFirst("~", home)
              else flagVal
            val outdir = new File(replacedHome)
            // Try to make the dir, if it fails we skip and go to the default
            if (!outdir.exists()) {
              outdir.mkdir()
            }
            if (!outdir.exists()) {
              // Ignore for now, can throw in the future
              // throw new InvalidPathException(outdir.getCanonicalPath, "Invalid directory name or parent doesn't exist")
            } else {
              OUTPUT_DIR = outdir.getCanonicalPath
            }
          } else if (flags.keySet.contains(flagname)) {
            // if not OUTDIR, use bool-flag rules and check for T/F
            flagVal match {
              case "TRUE" | "true" =>
                flags += flagname -> true
              case "FALSE" | "false" =>
                flags += flagname -> false
              case _ =>
              // Ignore for now, can throw in the future
              // throw new Exception(s"Flag $flagname must be one of: TRUE/true/FALSE/false.")
            }
          }
        }
      }
      src.close()
    }
    // If OUTDIR is not set or has an invalid value, default to making rundir = specdir/x/
    if (OUTPUT_DIR.isEmpty) {
      OUTPUT_DIR = Paths.get(System.getProperty("user.dir"), DEFAULT_OUTDIR).toString
    }
  }

  // Flags can be passed from options too, e.g. --profile or --write-intermediate
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

  /** Inside OUTDIR, create a directory for an individual run */
  def createRunDirectory(specName: String): Unit =
    if (runDirOpt.isEmpty) {
      val nicetime = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"yyyy-MM-dd_HH-mm-ss_"))
      val outdir = outDirAsFile
      if (!outdir.exists()) {
        outdir.mkdir()
      }
      // prefix for disambiguation
      val rundir = Files.createTempDirectory(Paths.get(outdir.getAbsolutePath), s"${specName}_" + nicetime)
      runDirOpt = Some(rundir)
    }
}

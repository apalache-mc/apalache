package at.forsyte.apalache.io

import java.io.File
import java.util.regex.Matcher
import scala.io.Source

object ReportGenerator {
  private val reportFile = "BugReport.md"
  private val reportTemplate = "issueTemplate.md"

  private object tags {
    val spec = "__SPEC"
    val cmd = "__CMD"
    val log = "__LOG"
    val version = "__VER"
    val os = "__OS"
    val jdk = "__JDK"
  }

  private def readSrcIntoString(src: Source): String =
    try src.mkString.strip()
    finally src.close()

  private def readFileIntoString(file: File): String =
    readSrcIntoString(Source.fromFile(file))

  private def readContentsOfFileInRunDir(filename: String): String = OutputManager.runDirPathOpt
    .map { runDir =>
      readFileIntoString(new File(runDir.toFile, filename))
    }
    .getOrElse("")

  // we drop the filename, since the path is local
  def getCMD(): String =
    readContentsOfFileInRunDir(OutputManager.Names.RunFile).split(" ").dropRight(1).mkString(" ")

  def getLog(): String =
    Matcher.quoteReplacement(readContentsOfFileInRunDir("detailed.log")) // handle $s in log

  def getSpec(file: File): String = readFileIntoString(file)

  // Can't access Version in IO, have to pass at call site
  def prepareReportFile(specFile: File, versionStr: String): String = {
    val template = readSrcIntoString(
        Source.fromResource(reportTemplate)
    )
    val specTxt = readFileIntoString(specFile)
    val cmd = getCMD()
    val log = getLog()
    val os = System.getProperty("os.name")
    val jdk = System.getProperty("java.version")

    val filledTemplate = template
      .replaceFirst(tags.spec, specTxt)
      .replaceFirst(tags.cmd, cmd)
      .replaceFirst(tags.log, log)
      .replaceFirst(tags.version, versionStr)
      .replaceFirst(tags.os, os)
      .replaceFirst(tags.jdk, jdk)

    OutputManager.withWriterRelativeToRunDir(reportFile) {
      _.println(filledTemplate)
    }

    new File(
        OutputManager.runDirPathOpt
          .getOrElse(throw new IllegalStateException("run directory is not configured"))
          .toFile, reportFile).getCanonicalPath
  }

}

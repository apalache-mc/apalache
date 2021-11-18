package at.forsyte.apalache.io

import java.io.File
import java.util.regex.Matcher
import scala.io.Source

object ReportGenerator {
  private val reportFile = "BugReport.md"

  private def readSrcIntoString(src: Source): String =
    try src.mkString.trim
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

  // Can't access Version in IO, have to pass at call site
  def prepareReportFile(specFile: File, versionStr: String): String = {
    val specTxt = readFileIntoString(specFile)
    val cmd = getCMD()
    val log = getLog()
    val os = System.getProperty("os.name")
    val jdk = System.getProperty("java.version")

    val filledTemplate = template.format(specTxt, cmd, log, versionStr, os, jdk)

    OutputManager.withWriterInRunDir(reportFile) {
      _.println(filledTemplate)
    }

    new File(OutputManager.runDir.toFile, reportFile).getCanonicalPath
  }

  private val template = """
      |<!-- Thank you for filing a report! Please ensure you have filled out all -->
      |<!-- sections, as it help us to address the problem effectively. -->
      |
      |## Input specification
      |
      |```
      |%s
      |```
      |
      |## The command line parameters used to run the tool
      |
      |```
      |%s
      |```
      |
      |## Expected behavior
      |
      |<!-- What did you expect to see? -->
      |
      |## Log files
      |
      |```
      |%s
      |```
      |
      |## System information
      |
      |- Apalache version: `%s`:
      |- OS: `%s`:
      |- JDK version: `%s`:
      |""".stripMargin

}

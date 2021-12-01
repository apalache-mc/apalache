package at.forsyte.apalache.io

import java.io.File
import java.util.regex.Matcher
import scala.io.Source

object ReportGenerator {
  private val reportFile = "BugReport.md"

  private def getFileOrEmptyStr(filename: String) = OutputManager.readContentsOfFileInRunDir(filename).getOrElse("")

  def getLog(): String =
    Matcher.quoteReplacement(getFileOrEmptyStr("detailed.log")) // handle $s in log

  // Can't access Version or Command in IO, have to pass at call site
  def prepareReportFile(cmdStr: String, versionStr: String): String = {
    val specTxt =
      OutputManager.getAllSrc.map(spec => s"```\n$spec\n````").getOrElse("<!-- TLA+ specification not found. -->")
    val log = getLog()
    val os = System.getProperty("os.name")
    val jdk = System.getProperty("java.version")

    val filledTemplate = template(specTxt, cmdStr, log, versionStr, os, jdk)

    OutputManager.withWriterInRunDir(reportFile) {
      _.println(filledTemplate)
    }

    new File(OutputManager.runDir.toFile, reportFile).getCanonicalPath
  }

  private def template(specTxt: String, cmd: String, log: String, version: String, os: String, jdk: String): String =
    s"""<!-- Thank you for filing a report! Please ensure you have filled out all -->
      |<!-- sections, as it help us to address the problem effectively. -->
      |
      |## Input specification
      |
      |$specTxt
      |
      |## The command line parameters used to run the tool
      |
      |```
      |$cmd
      |```
      |
      |## Expected behavior
      |
      |<!-- What did you expect to see? -->
      |
      |## Log files
      |
      |```
      |$log
      |```
      |
      |## System information
      |
      |- Apalache version: `$version`:
      |- OS: `$os`:
      |- JDK version: `$jdk`:
      |""".stripMargin

}

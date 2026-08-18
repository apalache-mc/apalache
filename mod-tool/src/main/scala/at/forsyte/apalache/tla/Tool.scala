package at.forsyte.apalache.tla

// Generated from the build.sbt file by the buildInfo plugin
import apalache.BuildInfo
import at.forsyte.apalache.infra._
import at.forsyte.apalache.infra.log.LogbackConfigurator
import at.forsyte.apalache.io.config._
import at.forsyte.apalache.io.config.Constants.{CONFIG, ENABLE_STATS}
import at.forsyte.apalache.io.{ConfigurationError, OutputManager, ReportGenerator}
import at.forsyte.apalache.tla.tooling.opt._
import com.typesafe.scalalogging.LazyLogging
import org.backuity.clist.Cli
import util.ExecutionStatisticsCollector

import java.time.LocalDateTime
import java.time.temporal.ChronoUnit
import scala.jdk.CollectionConverters._
import scala.util.{Failure, Random, Success, Try}

/**
 * Command line access to the APALACHE tools.
 *
 * @author
 *   Igor Konnov
 */
object Tool extends LazyLogging {
  lazy val ISSUES_LINK: String = "[https://github.com/apalache-mc/apalache/issues]"

  /**
   * Run the tool in the standalone mode with the provided arguments. This method calls [[java.lang.System.exit]] with
   * the computed exit code. To call the tool without System.exit, use [[run]].
   *
   * @param args
   *   the command line arguments
   */
  def main(args: Array[String]): Unit = {
    try {
      System.exit(run(args))
    } catch {
      case _: OutOfMemoryError =>
        // We usually catch this in `handleExceptions` below.
        // If it is caught here, logging has not been set up yet, so print directly to `Console.err`.
        Console.err.println(s"Error: Ran out of heap memory (max JVM memory: ${Runtime.getRuntime.maxMemory})")
        Console.err.println(s"To increase available heap memory, see the manual:")
        Console.err.println("  [https://apalache-mc.org/docs/apalache/running.html#supplying-jvm-arguments]")
        Console.out.println(s"EXITCODE: ERROR (${ExitCodes.ERROR})")
        System.exit(ExitCodes.ERROR)
    }
  }

  private def outputAndLogConfig(cmd: ApalacheCommand, cfg: ApalacheConfig): Try[Unit] = for {
    initialization <- {
      val result = ApalacheConfigResolver.resolveCommandInitialization(cfg)
      if (result.isSuccess) Try(result.requireValue())
      else Failure(new ConfigurationError(result.errors.mkString("; ")))
    }
    _ <- Try(OutputManager.configure(initialization))
  } yield {
    println(s"Output directory: ${OutputManager.runDir.normalize()}")
    OutputManager.withWriterInRunDir(OutputManager.RunFile)(
        _.println(s"${cmd.env} ${cmd.label} ${cmd.invocation}")
    )

    // Write the application configuration, if debug is enabled
    if (initialization.common.debug) {
      OutputManager.withWriterInRunDir("application-config.json") { writer =>
        writer.print(ApalacheConfigJsonParser.write(cfg.mergeWithDefaults, usePrettyPrinter = true))
      }
    }

    // force our programmatic logback configuration, as the autoconfiguration works unpredictably
    new LogbackConfigurator(Some(OutputManager.runDir), OutputManager.additionalRunDir).configureDefaultContext()
    // TODO: update workers when the multicore branch is integrated
    logger.info(s"# APALACHE version: ${BuildInfo.version} | build: ${BuildInfo.build}")

    submitStatisticsIfEnabled(Map("tool" -> "apalache", "mode" -> cmd.label, "workers" -> "1"))
  }

  /** Build the CLI configuration, then select and merge at most one file-based configuration. */
  private def loadConfig(cmd: ApalacheCommand): ConfigParseResult[ApalacheConfig] = {
    val primary = cmd.toConfig
    if (primary.isSuccess) {
      ConfigParseResult.withWarnings(
          ApalacheConfigLoader.load(primary.requireValue()),
          primary.warnings,
      )
    } else {
      ConfigParseResult.failureFrom(primary)
    }
  }

  /**
   * Run the tool in a library mode, that is, with a call to System.exit.
   *
   * @param args
   *   the command line arguments
   * @return
   *   the exit code; as usual, 0 means success.
   */
  def run(args: Array[String]): Int = OutputManager.withScope {
    runInScope(args)
  }

  private def runInScope(args: Array[String]): Int = {
    // Configure the silent logger first. Otherwise, Apache Commons spills a lot of text to the console.
    new LogbackConfigurator(None, None).configureDefaultContext()
    // first, call the arguments parser, which can also handle the standard commands such as version
    val cli = Cli
      .parse(args)
      .withProgramName("apalache-mc")
      .version(BuildInfo.version)
      .withCommands(
          new ParseCmd,
          new CheckCmd,
          new SimulateCmd,
          new TypeCheckCmd,
          new TestCmd,
          new ConfigCmd,
          new ServerCmd,
          new TranspileCmd,
          new TraceeCmd,
      )

    cli match {
      // A standard option, e.g., --version or --help. No header, no timer, no noise
      case None => ExitCodes.OK
      // One of our commands.
      case Some(cmd) => {
        val configResult = loadConfig(cmd)
        printStatsConfig()

        val exitcode =
          if (!configResult.isSuccess) {
            logger.error(configResult.errors.mkString("Configuration error: ", "; ", ""))
            ExitCodes.ERROR
          } else {
            val config = configResult.requireValue()
            outputAndLogConfig(cmd, config) match {
              case Failure(cfgErr) => {
                logger.error(s"Configuration error: ${cfgErr.getMessage}")
                ExitCodes.ERROR
              }
              case Success(()) => {
                configResult.warnings.foreach(warning => logger.warn(warning))
                val startTime = LocalDateTime.now()
                try {
                  runCommand(cmd, config)
                } finally {
                  printTimeDiff(startTime)
                }
              }
            }
          }

        if (exitcode == ExitCodes.OK) {
          Console.out.println("EXITCODE: OK")
        } else {
          Console.out.println(s"EXITCODE: ERROR ($exitcode)")
        }
        exitcode
      }
    }
  }

  // Execute the program specified by the subcommand cmd, handling errors as needed
  private def runCommand(cmd: ApalacheCommand, config: ApalacheConfig): ExitCodes.TExitCode = {
    def readSourceCode(): Option[String] = config.source.flatMap(_.readUtf8.value)

    try {
      cmd.run(config) match {
        case Left((errorCode, failMsg)) => { logger.info(failMsg); errorCode }
        case Right(msg)                 => { logger.info(msg); ExitCodes.OK }
      }
    } catch {
      case e: AdaptedException =>
        e.err match {
          case NormalErrorMessage(text) => logger.error(text)
          case FailureMessage(text)     => { logger.error(text, e); generateBugReport(e, cmd, readSourceCode()) }
        }
        ExitCodes.ERROR

      // Raised on invalid or erroneous property files or tuning options arguments
      case e: PassOptionException =>
        logger.error(e.getMessage)
        ExitCodes.ERROR

      case e: Throwable =>
        logger.error("Unhandled exception", e)
        generateBugReport(e, cmd, readSourceCode())
        ExitCodes.ERROR
    }
  }

  private def printTimeDiff(startTime: LocalDateTime): Unit = {
    val endTime = LocalDateTime.now()
    logger.info("It took me %d days %2d hours %2d min %2d sec"
          .format(ChronoUnit.DAYS.between(startTime, endTime), ChronoUnit.HOURS.between(startTime, endTime) % 24,
              ChronoUnit.MINUTES.between(startTime, endTime) % 60, ChronoUnit.SECONDS.between(startTime, endTime) % 60))
    logger.info("Total time: %d.%d sec"
          .format(ChronoUnit.SECONDS.between(startTime, endTime), ChronoUnit.MILLIS.between(startTime, endTime) % 1000))
  }

  private def printStatsConfig(): Unit = {
    if (new ExecutionStatisticsCollector().isEnabled) {
      // Statistic collection is enabled. Thank the user
      Console.println("# Usage statistics is ON. Thank you!")
      Console.println(s"# If you have changed your mind, disable the statistics with $CONFIG --$ENABLE_STATS=false.")
    } else {
      // Statistics collection is not enabled. Cry for help.
      Console.println("# Usage statistics is OFF. We care about your privacy.")
      Console.println(
          s"# If you want to help our project, consider enabling statistics with $CONFIG --$ENABLE_STATS=true.")
    }
    Console.println("")
  }

  // If the user has opted-in, collect statistics with the code from tlatools:
  //
  // https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/util/ExecutionStatisticsCollector.java
  //
  // See how TLC does it:
  // https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/TLC.java
  private def submitStatisticsIfEnabled(commandParams: Map[String, String]): Unit = {
    val statCollector = new ExecutionStatisticsCollector()
    if (statCollector.isEnabled) {
      val params = new java.util.HashMap[String, String]()
      params.put("ver", "apalache-%s-%s".format(BuildInfo.version, BuildInfo.build))
      params.put("osName", System.getProperty("os.name"))
      params.put("osArch", System.getProperty("os.arch"))
      params.put("osVersion", System.getProperty("os.version"))
      params.put("jvmVendor", System.getProperty("java.vendor"))
      params.put("jvmVersion", System.getProperty("java.version"))
      params.put("jvmArch", System.getProperty("os.arch"))
      params.put("cores", Runtime.getRuntime.availableProcessors.toString)
      val heapMemory = Runtime.getRuntime.maxMemory / 1024L / 1024L
      params.put("jvmHeapMem", heapMemory.toString)
      val saltSec = Random.nextInt(600) // a random salt to introduce a bit of entropy in the timestamp
      val timestampSec = System.currentTimeMillis() / 1000 - saltSec
      params.put("ts", timestampSec.toString)
      params.putAll(commandParams.asJava)
      // fix #288: one more parameter to keep compatibility with TLC reporting
      params.put("jvmOffHeapMem", "0")
      statCollector.collect(params)
    }
  }

  private def generateBugReport(e: Throwable, cmd: ApalacheCommand, sourceText: Option[String]): Unit = {
    val absPath = ReportGenerator.prepareReportFile(
        sourceText,
        cmd.invocation.split(" ").dropRight(1).mkString(" "),
        s"${BuildInfo.version} build ${BuildInfo.build}",
    )
    Console.err.println(
        s"""|Please report an issue at $ISSUES_LINK: $e
            |A bug report template has been generated at [$absPath].
            |If you choose to use it, please complete the template with a description of the expected behavior and impact.""".stripMargin
    )
  }
}

package at.forsyte.apalache.tla

// Generated from the build.sbt file by the buildInfo plugin
import apalache.BuildInfo
import at.forsyte.apalache.infra._
import at.forsyte.apalache.infra.log.LogbackConfigurator
import at.forsyte.apalache.infra.passes.{PassChainExecutor, ToolModule, WriteablePassOptions}
import at.forsyte.apalache.io.{ConfigManager, ConfigurationError, OutputManager, ReportGenerator}
import at.forsyte.apalache.tla.bmcmt.config.{CheckerModule, ReTLAToVMTModule}
import at.forsyte.apalache.tla.bmcmt.rules.vmt.TlaExToVMTWriter
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.tooling.opt._
import at.forsyte.apalache.tla.typecheck.passes.TypeCheckerModule
import at.forsyte.apalache.shai
import com.google.inject.{Guice, Injector}
import com.typesafe.scalalogging.LazyLogging
import org.apache.commons.configuration2.builder.fluent.Configurations
import org.apache.commons.configuration2.ex.ConfigurationException
import org.backuity.clist.Cli
import util.ExecutionStatisticsCollector
import util.ExecutionStatisticsCollector.Selection

import java.io.{File, FileNotFoundException}
import java.time.LocalDateTime
import java.time.temporal.ChronoUnit
import scala.jdk.CollectionConverters._
import scala.util.Random

/**
 * Command line access to the APALACHE tools.
 *
 * @author
 *   Igor Konnov
 */
object Tool extends LazyLogging {
  lazy val ISSUES_LINK: String = "[https://github.com/informalsystems/apalache/issues]"

  /**
   * Run the tool in the standalone mode with the provided arguments. This method calls [[System.exit]] with the
   * computed exit code. To call the tool without System.exit, use [[run]].
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
        Console.err.println("  [https://apalache.informal.systems/docs/apalache/running.html#supplying-jvm-arguments]")
        Console.out.println(s"EXITCODE: ERROR (${ExitCodes.ERROR})")
        System.exit(ExitCodes.ERROR)
    }
  }

  // Returns `Left(errmsg)` in case of configuration errors
  private def outputAndLogConfig(cmd: General): Either[String, Unit] = {
    ConfigManager(cmd).map { cfg =>
      try {
        OutputManager.configure(cfg)
      } catch {
        case e: ConfigurationError => return Left(e.getMessage)
      }
      // We currently use dummy files for some commands, so we skip here on non-existing files
      if (cmd.file.getName.endsWith(".tla") && cmd.file.exists()) {
        OutputManager.initSourceLines(cmd.file)
      }
      println(s"Output directory: ${OutputManager.runDir.normalize()}")
      OutputManager.withWriterInRunDir(OutputManager.Names.RunFile)(
          _.println(s"${cmd.env} ${cmd.label} ${cmd.invocation}")
      )
      // force our programmatic logback configuration, as the autoconfiguration works unpredictably
      new LogbackConfigurator(OutputManager.runDirPathOpt, OutputManager.customRunDirPathOpt).configureDefaultContext()
      // TODO: update workers when the multicore branch is integrated
      logger.info(s"# APALACHE version: ${BuildInfo.version} | build: ${BuildInfo.build}")

      submitStatisticsIfEnabled(Map("tool" -> "apalache", "mode" -> cmd.label, "workers" -> "1"))
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
  def run(args: Array[String]): Int = {
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
      )

    cli match {
      // A standard option, e.g., --version or --help. No header, no timer, no noise
      case None => ExitCodes.OK
      // One of our commands.
      case Some(cmd) => {

        printStatsConfig()

        val exitcode = outputAndLogConfig(cmd) match {
          case Left(configurationErrorMessage) => {
            logger.error(s"Configuration error: ${configurationErrorMessage}")
            ExitCodes.ERROR
          }
          case Right(()) => {
            val startTime = LocalDateTime.now()
            try {
              cmd match {
                case parse: ParseCmd =>
                  runForModule(runParse, new ParserModule, parse)

                case simulate: SimulateCmd =>
                  // simulation is just a special case of checking, which has additional parameters passed via SimulateCmd
                  runForModule(runCheck, new CheckerModule, simulate)

                case check: CheckCmd =>
                  runForModule(runCheck, new CheckerModule, check)

                case test: TestCmd =>
                  runForModule(runTest, new CheckerModule, test)

                case typecheck: TypeCheckCmd =>
                  runForModule(runTypeCheck, new TypeCheckerModule, typecheck)

                case server: ServerCmd =>
                  runForModule(runServer, new CheckerModule, server)

                case constrain: TranspileCmd =>
                  runForModule(runConstrain, new ReTLAToVMTModule, constrain)

                case config: ConfigCmd =>
                  configure(config)
              }
            } finally {
              printTimeDiff(startTime)
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

  private def printTimeDiff(startTime: LocalDateTime): Unit = {
    val endTime = LocalDateTime.now()
    logger.info("It took me %d days %2d hours %2d min %2d sec"
          .format(ChronoUnit.DAYS.between(startTime, endTime), ChronoUnit.HOURS.between(startTime, endTime) % 24,
              ChronoUnit.MINUTES.between(startTime, endTime) % 60, ChronoUnit.SECONDS.between(startTime, endTime) % 60))
    logger.info("Total time: %d.%d sec"
          .format(ChronoUnit.SECONDS.between(startTime, endTime), ChronoUnit.MILLIS.between(startTime, endTime) % 1000))
  }

  // Set the pass options from the cli configs shared between all commands
  private def setCommonOptions(cli: General, options: WriteablePassOptions): Unit = {
    options.set("general.debug", cli.debug)
    options.set("smt.prof", cli.smtprof)
    options.set("general.features", cli.features)

    // TODO: Remove pass option, and just rely on OutputManager config
    options.set("io.outdir", OutputManager.outDir)
  }

  private def runAndExit(
      executor: PassChainExecutor,
      msgIfOk: TlaModule => String,
      msgIfFail: String): ExitCodes.TExitCode = {
    val result = executor.run()
    result match {
      case Left(errorCode) =>
        logger.info(msgIfFail)
        errorCode
      case Right(module) =>
        logger.info(msgIfOk(module))
        ExitCodes.OK
    }
  }

  private def setCoreOptions(executor: PassChainExecutor, cmd: AbstractCheckerCmd): Unit = {
    logger.info {
      val environment = if (cmd.env != "") s"(${cmd.env}) " else ""
      s"Checker options: ${environment}${cmd.name} ${cmd.invocation}"
    }
    executor.options.set("parser.filename", cmd.file.getAbsolutePath)
    if (cmd.config != "")
      executor.options.set("checker.config", cmd.config)
    if (cmd.init != "")
      executor.options.set("checker.init", cmd.init)
    if (cmd.next != "")
      executor.options.set("checker.next", cmd.next)
    if (cmd.inv != "")
      executor.options.set("checker.inv", List(cmd.inv))
    if (cmd.cinit != "")
      executor.options.set("checker.cinit", cmd.cinit)
    executor.options.set("checker.length", cmd.length)
  }

  private def runParse(executor: PassChainExecutor, parse: ParseCmd): Int = {
    // here, we implement a terminal pass to get the parse results

    // init
    logger.info("Parse " + parse.file)

    executor.options.set("parser.filename", parse.file.getAbsolutePath)
    parse.output.foreach(executor.options.set("io.output", _))

    // NOTE Must go after all other options are set due to side-effecting
    // behavior of current OutmputManager configuration
    setCommonOptions(parse, executor.options)

    runAndExit(
        executor,
        m => {
          s"Parsed successfully\nRoot module: ${m.name} with ${m.declarations.length} declarations."
        },
        "Parser has failed",
    )
  }

  private def runCheck(executor: PassChainExecutor, check: CheckCmd): Int = {
    setCoreOptions(executor, check)

    var tuning =
      if (check.tuningOptionsFile != "") loadProperties(check.tuningOptionsFile) else Map[String, String]()
    tuning = overrideProperties(tuning, check.tuningOptions)

    check match {
      case sim: SimulateCmd =>
        // propagate the simulator options to the tuning options, so the model checker can easily pick them
        tuning += "search.simulation" -> "true"
        tuning += "search.simulation.maxRun" -> sim.maxRun.toString
        tuning += "search.simulation.saveRuns" -> sim.saveRuns.toString

      case _ => ()
    }
    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    executor.options.set("general.tuning", tuning)
    executor.options.set("checker.nworkers", check.nworkers)
    executor.options.set("checker.discardDisabled", check.discardDisabled)
    executor.options.set("checker.noDeadlocks", check.noDeadlocks)
    executor.options.set("checker.algo", check.algo)
    executor.options.set("checker.smt-encoding", check.smtEncoding)
    executor.options.set("checker.maxError", check.maxError)
    if (check.view != "")
      executor.options.set("checker.view", check.view)
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    executor.options.set("typechecker.inferPoly", true)

    // NOTE Must go after all other options are set due to side-effecting
    // behavior of current OutmputManager configuration
    setCommonOptions(check, executor.options)

    runAndExit(
        executor,
        _ => "Checker reports no error up to computation length " + check.length,
        "Checker has found an error",
    )
  }

  private def runTest(executor: PassChainExecutor, test: TestCmd): Int = {
    // This is a special version of the `check` command that is tuned towards testing scenarios

    logger.info("Checker options: filename=%s, before=%s, action=%s, after=%s"
          .format(test.file, test.before, test.action, test.assertion))

    // Tune for testing:
    //   1. Check the invariant only after the action took place.
    //   2. Randomize
    val seed = Math.abs(System.currentTimeMillis().toInt)
    val tuning = Map("search.invariantFilter" -> "1", "smt.randomSeed" -> seed.toString)
    logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

    executor.options.set("general.tuning", tuning)
    executor.options.set("parser.filename", test.file.getAbsolutePath)
    executor.options.set("checker.init", test.before)
    executor.options.set("checker.next", test.action)
    executor.options.set("checker.inv", List(test.assertion))
    if (test.cinit != "") {
      executor.options.set("checker.cinit", test.cinit)
    }
    executor.options.set("checker.nworkers", 1)
    // check only one instance of the action
    executor.options.set("checker.length", 1)
    // no preliminary pruning of disabled transitions
    executor.options.set("checker.discardDisabled", false)
    executor.options.set("checker.noDeadlocks", false)
    // prefer the offline mode as we have a single query
    executor.options.set("checker.algo", "offline")
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    executor.options.set("typechecker.inferPoly", true)
    // NOTE Must go after all other options are set due to side-effecting
    // behavior of current OutmputManager configuration
    setCommonOptions(test, executor.options)

    runAndExit(
        executor,
        _ => "No example found",
        "Found a violation of the postcondition. Check violation.tla.",
    )
  }

  private def runTypeCheck(executor: PassChainExecutor, typecheck: TypeCheckCmd): Int = {
    // type checker

    logger.info("Type checking " + typecheck.file)

    executor.options.set("parser.filename", typecheck.file.getAbsolutePath)
    typecheck.output.foreach(executor.options.set("io.output", _))
    executor.options.set("typechecker.inferPoly", typecheck.inferPoly)

    // NOTE Must go after all other options are set due to side-effecting
    // behavior of current OutmputManager configuration
    setCommonOptions(typecheck, executor.options)

    runAndExit(
        executor,
        _ => "Type checker [OK]",
        "Type checker [FAILED]",
    )
  }

  private def runServer(executor: PassChainExecutor, server: ServerCmd): Int = {
    logger.info("Starting server...")

    // NOTE Must go after all other options are set due to side-effecting
    // behavior of current OutputManager configuration
    setCommonOptions(server, executor.options)

    shai.v1.RpcServer.main(Array())
    ExitCodes.OK
  }

  private def runConstrain(executor: PassChainExecutor, constrain: TranspileCmd): Int = {
    setCoreOptions(executor, constrain)
    // for now, enable polymorphic types. We probably want to disable this option for the type checker
    executor.options.set("typechecker.inferPoly", true)

    // NOTE Must go after all other options are set due to side-effecting
    // behavior of current OutmputManager configuration
    setCommonOptions(constrain, executor.options)

    val outFilePath = OutputManager.runDirPathOpt
      .map { p =>
        p.resolve(TlaExToVMTWriter.outFileName).toAbsolutePath
      }
      .getOrElse(TlaExToVMTWriter.outFileName)

    runAndExit(
        executor,
        _ => s"VMT constraints successfully generated at\n$outFilePath",
        "Failed to generate constraints",
    )
  }

  private def loadProperties(filename: String): Map[String, String] = {
    // use an apache-commons library, as it supports variable substitution
    try {
      val config = new Configurations().properties(new File(filename))
      // access configuration properties
      var map = Map[String, String]()
      for (name: String <- config.getKeys.asScala) {
        map += (name -> config.getString(name))
      }
      map
    } catch {
      case _: FileNotFoundException =>
        throw new PassOptionException(s"The properties file $filename not found")

      case e: ConfigurationException =>
        throw new PassOptionException(s"Error in the properties file $filename: ${e.getMessage}")
    }
  }

  private def overrideProperties(props: Map[String, String], propsAsString: String): Map[String, String] = {
    def parseKeyValue(text: String): (String, String) = {
      val parts = text.split('=')
      if (parts.length != 2 || parts.head.trim == "" || parts(1) == "") {
        throw new PassOptionException(s"Expected key=value in --tuning-options=$propsAsString")
      } else {
        // trim to remove surrounding whitespace from the key, but allow the value to have white spaces
        (parts.head.trim, parts(1))
      }
    }

    val hereProps = {
      if (propsAsString.trim.nonEmpty) {
        propsAsString.split(':').map(parseKeyValue).toMap
      } else {
        Map.empty
      }
    }
    // hereProps may override the values in props
    props ++ hereProps
  }

  private def runForModule[C <: General](runner: (PassChainExecutor, C) => Int, module: ToolModule, cmd: C): Int = {
    val injector = Guice.createInjector(module)
    val passes = module.passes.zipWithIndex.map { case (p, i) =>
      injector.getInstance(p).withNumber(i)
    }
    val options = injector.getInstance(classOf[WriteablePassOptions])
    val executor = new PassChainExecutor(options, passes)

    handleExceptions(runner, injector, executor, cmd)
  }

  private def handleExceptions[C <: General](
      runner: (PassChainExecutor, C) => Int,
      injector: Injector,
      executor: PassChainExecutor,
      cmd: C): Int = {
    val adapter = injector.getInstance(classOf[ExceptionAdapter])
    try {
      runner(executor, cmd)
    } catch {
      case e: Throwable if adapter.toMessage.isDefinedAt(e) =>
        adapter.toMessage(e) match {
          case NormalErrorMessage(text) =>
            logger.error(text)

          case FailureMessage(text) =>
            logger.error(text, e)
            val absPath = ReportGenerator.prepareReportFile(
                cmd.invocation.split(" ").dropRight(1).mkString(" "),
                s"${BuildInfo.version} build ${BuildInfo.build}",
            )
            Console.err.println(
                s"Please report an issue at $ISSUES_LINK: $e\nA bug report template has been generated at [$absPath].\nIf you choose to use it, please complete the template with a description of the expected behavior."
            )

        }
        ExitCodes.ERROR

      case e: PassOptionException =>
        logger.error(e.getMessage)
        ExitCodes.ERROR

      case e: Throwable =>
        Console.err.println("Please report an issue at: " + ISSUES_LINK, e)
        logger.error("Unhandled exception", e)
        ExitCodes.ERROR
    }
  }

  private def printStatsConfig(): Unit = {
    if (new ExecutionStatisticsCollector().isEnabled) {
      // Statistic collection is enabled. Thank the user
      Console.println("# Usage statistics is ON. Thank you!")
      Console.println("# If you have changed your mind, disable the statistics with config --enable-stats=false.")
    } else {
      // Statistics collection is not enabled. Cry for help.
      Console.println("# Usage statistics is OFF. We care about your privacy.")
      Console.println(
          "# If you want to help our project, consider enabling statistics with config --enable-stats=true.")
    }
    Console.println("")
  }

  private def configure(config: ConfigCmd): Int = {
    logger.info("Configuring Apalache")
    config.submitStats match {
      case Some(isEnabled) =>
        val warning = "Unable to update statistics configuration. The other features will keep working."

        if (!configDirExistsOrCreated()) {
          logger.warn(warning)
        } else {
          val statCollector = new ExecutionStatisticsCollector()
          // protect against potential exceptions in the tla2tools code
          try {
            if (isEnabled) {
              statCollector.set(Selection.ON)
              logger.info("Statistics collection is ON.")
              logger.info("This also enabled TLC and TLA+ Toolbox statistics.")
            } else {
              statCollector.set(Selection.NO_ESC)
              logger.info("Statistics collection is OFF.")
              logger.info("This also disabled TLC and TLA+ Toolbox statistics.")
            }
          } catch {
            case e: Exception =>
              logger.warn(e.getMessage)
              logger.warn(warning)
          }
        }

      case None =>
        ()
    }

    ExitCodes.OK
  }

  private def configDirExistsOrCreated(): Boolean = {
    // A temporary fix for the issue #762: create ~/.tlaplus if it does not exist
    val configDir = new File(System.getProperty("user.home", ""), ".tlaplus")
    if (configDir.exists()) {
      true
    } else {
      try {
        configDir.mkdir()
        true
      } catch {
        case e: Exception =>
          logger.warn(e.getMessage)
          logger.warn(s"Unable to create the directory $configDir.")
          false
      }
    }
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
}

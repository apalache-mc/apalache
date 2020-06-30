package at.forsyte.apalache.tla

import java.io.{File, FileNotFoundException}
import java.nio.file.{Files, Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.time.temporal.ChronoUnit

import at.forsyte.apalache.infra.log.LogbackConfigurator
import at.forsyte.apalache.infra.passes.{PassChainExecutor, TlaModuleMixin}
import at.forsyte.apalache.infra.{ExceptionAdapter, FailureMessage, NormalErrorMessage, PassOptionException}
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.tooling.Version
import at.forsyte.apalache.tla.tooling.opt.{CheckCmd, ParseCmd}
import com.google.inject.{Guice, Injector}
import com.typesafe.scalalogging.LazyLogging
import org.apache.commons.configuration2.builder.fluent.Configurations
import org.apache.commons.configuration2.ex.ConfigurationException
import org.backuity.clist.{Cli, Command}

import scala.collection.JavaConverters._

/**
  * Command line access to the APALACHE tools.
  *
  * @author Igor Konnov
  */
object Tool extends App with LazyLogging {
  lazy val ISSUES_LINK: String = "[https://github.com/konnov/apalache/issues]"
  lazy val ERROR_EXIT_CODE = 99
  lazy val OK_EXIT_CODE = 0

  /**
    * Run the tool in the standalone mode with the provided arguments.
    * This method calls System.exit with the computed exit code.
    * If you like to call the tool without System.exit, use the the Tool#run.
    *
    * @param args the command line arguments
    */
  override def main(args: Array[String]): Unit = {
    val exitcode = run(args)
    if (exitcode == OK_EXIT_CODE) {
      Console.out.println("EXITCODE: OK")
    } else {
      Console.out.println(s"EXITCODE: ERROR ($exitcode)")
    }
    System.exit(exitcode)
  }

  /**
    * Run the tool in a library mode, that is, with a call to System.exit.
    *
    * @param args the command line arguments
    * @return the exit code; as usual, 0 means success.
    */
  def run(args: Array[String]): Int = {
    Console.println("# APALACHE version %s build %s".format(Version.version, Version.build))
    Console.println("#")
    Console.println("# WARNING: This tool is in the experimental stage.")
    Console.println("#          Please report bugs at: " + ISSUES_LINK)
    Console.println("")
    // force our programmatic logback configuration, as the autoconfiguration works unpredictably
    new LogbackConfigurator().configureDefaultContext()
    // start
    val startTime = LocalDateTime.now()
    val parseCmd = new ParseCmd
    val checkCmd = new CheckCmd
    try {
      Cli.parse(args).withProgramName("apalache-mc").version(Version.version)
        .withCommands(parseCmd, checkCmd) match {
        case Some(parse: ParseCmd) =>
          logger.info("Parse " + parse.file)
          val injector = injectorFactory(parseCmd)
          handleExceptions(injector, runParse(injector, parse, _))

        case Some(check: CheckCmd) =>
          logger.info("Checker options: filename=%s, init=%s, next=%s, inv=%s"
            .format(check.file, check.init, check.next, check.inv))
          val injector = injectorFactory(check)
          handleExceptions(injector, runCheck(injector, check, _))

        case _ =>
          OK_EXIT_CODE // nothing to do
      }
    } finally {
      printTimeDiff(startTime)
    }
  }

  private def printTimeDiff(startTime: LocalDateTime): Unit = {
    val endTime = LocalDateTime.now()
    logger.info("It took me %d days %2d hours %2d min %2d sec"
      .format(ChronoUnit.DAYS.between(startTime, endTime),
        ChronoUnit.HOURS.between(startTime, endTime) % 23,
        ChronoUnit.MINUTES.between(startTime, endTime) % 60,
        ChronoUnit.SECONDS.between(startTime, endTime) % 60))
    logger.info("Total time: %d.%d sec"
      .format(ChronoUnit.SECONDS.between(startTime, endTime),
        ChronoUnit.MILLIS.between(startTime, endTime) % 1000))
  }

  private def runParse(injector: Injector, parse: ParseCmd, u: Unit): Unit = {
    // here, we implement a terminal pass to get the parse results
    val executor = injector.getInstance(classOf[PassChainExecutor])
    executor.options.set("io.outdir", createOutputDir())
    executor.options.set("parser.filename", parse.file.getAbsolutePath)
    executor.options.set("parser.output", parse.output)

    val result = executor.run()
    if (result.isDefined) {
      logger.info("Parsed successfully")
      val tlaModule = result.get.asInstanceOf[TlaModuleMixin].unsafeGetModule
      logger.info("Root module: %s with %d declarations".format(tlaModule.name,
        tlaModule.declarations.length))
    } else {
      logger.info("Parser has failed")
    }
  }

  private def runCheck(injector: Injector, check: CheckCmd, u: Unit): Unit = {
    val executor = injector.getInstance(classOf[PassChainExecutor])
    executor.options.set("io.outdir", createOutputDir())
    val tuning =
      if (check.tuning != "") {
        loadProperties(check.tuning)
      } else {
        Map[String, String]()
      }
    executor.options.set("general.tuning", tuning)
    executor.options.set("general.debug", check.debug)
    executor.options.set("smt.prof", check.smtprof)
    executor.options.set("parser.filename", check.file.getAbsolutePath)
    if (check.config != "")
      executor.options.set("checker.config", check.config)
    if (check.init != "")
      executor.options.set("checker.init", check.init)
    if (check.next != "")
      executor.options.set("checker.next", check.next)
    if (check.inv != "")
      executor.options.set("checker.inv", List(check.inv))
    if (check.cinit != "")
      executor.options.set("checker.cinit", check.cinit)
    executor.options.set("checker.length", check.length)
    executor.options.set("checker.search", check.search)

    val result = executor.run()
    if (result.isDefined) {
      logger.info("Checker reports no error up to computation length " + check.length)
    } else {
      logger.info("Checker has found an error")
    }
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

  private def createOutputDir(): Path = {
    // here we use the order 'hours-minutes and then the date', as it is much easier to use with completion
    val nicetime = LocalDateTime.now().format(DateTimeFormatter.ofPattern("HH.mm-dd.MM.uuuu-"))
    val xdir = new File(System.getProperty("user.dir"), "x")
    if (!xdir.exists()) {
      xdir.mkdir()
    }
    Files.createTempDirectory(Paths.get(xdir.getAbsolutePath), nicetime)
  }

  private def injectorFactory(cmd: Command): Injector = {
    cmd match {
      case _: ParseCmd => Guice.createInjector(new ParserModule)
      case _: CheckCmd => Guice.createInjector(new CheckerModule)
      case _ => throw new RuntimeException("Unexpected command: " + cmd)
    }
  }

  private def handleExceptions(injector: Injector, fun: Unit => Unit): Int = {
    val adapter = injector.getInstance(classOf[ExceptionAdapter])

    try {
      fun()
      Tool.OK_EXIT_CODE
    } catch {
      case e: Exception if adapter.toMessage.isDefinedAt(e) =>
        adapter.toMessage(e) match {
          case NormalErrorMessage(text) =>
            logger.error(text)

          case FailureMessage(text) =>
            Console.err.println("Please report an issue at: " + ISSUES_LINK, e)
            logger.error(text, e)
        }
        Tool.ERROR_EXIT_CODE

      case e: PassOptionException =>
        logger.error(e.getMessage)
        Tool.ERROR_EXIT_CODE

      case e: Throwable =>
        Console.err.println("Please report an issue at: " + ISSUES_LINK, e)
        logger.error("Unhandled exception", e)
        Tool.ERROR_EXIT_CODE
    }
  }
}

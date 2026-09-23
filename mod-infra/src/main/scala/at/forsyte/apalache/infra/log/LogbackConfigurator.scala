package at.forsyte.apalache.infra.log

import ch.qos.logback.classic.filter.ThresholdFilter
import ch.qos.logback.classic.spi.{Configurator, ILoggingEvent}
import ch.qos.logback.classic.{Level, LoggerContext, PatternLayout}
import ch.qos.logback.core.encoder.LayoutWrappingEncoder
import ch.qos.logback.core.spi.ContextAwareBase
import ch.qos.logback.core.{ConsoleAppender, FileAppender}
import org.slf4j.LoggerFactory

import java.io.File
import java.nio.file.Path

/**
 * A hand-written configurator for logback, as it fails to discover logback-old.xml in some environments.
 *
 * @author
 *   Igor Konnov
 */
// TODO Configure to take OutputManager as parameter?
class LogbackConfigurator(runDir: Option[Path], customRunDir: Option[Path]) extends ContextAwareBase with Configurator {
  def configureDefaultContext(): Unit = {
    val loggerContext = awaitLoggerContext(System.nanoTime() + java.time.Duration.ofSeconds(30).toNanos)
    setContext(loggerContext)
    runDir match {
      case Some(_) => configure(loggerContext)
      case None    => configureConsoleOnlyWarn(loggerContext)
    }
  }

  /**
   * Get the logback logger context, waiting for SLF4J's one-time provider initialization if needed. While another
   * thread is running the initialization, `LoggerFactory.getILoggerFactory` returns a `SubstituteLoggerFactory`
   * instead of the logback context.
   *
   * Note that SLF4J offers no API to await the initialization, so we have to poll. This is a long-standing unsolved
   * issue upstream: https://jira.qos.ch/browse/SLF4J-167
   */
  @scala.annotation.tailrec
  private def awaitLoggerContext(deadlineNanos: Long): LoggerContext =
    LoggerFactory.getILoggerFactory match {
      case context: LoggerContext => context
      case other if System.nanoTime() < deadlineNanos =>
        Thread.sleep(10)
        awaitLoggerContext(deadlineNanos)
      case other =>
        throw new IllegalStateException(
            s"SLF4J did not initialize a logback LoggerContext; got ${other.getClass.getName}")
    }

  def configureConsoleOnlyWarn(loggerContext: LoggerContext): Unit = {
    loggerContext.reset() // forget everything that was configured automagically
    val rootLogger = loggerContext.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME)
    val consoleAppender = mkConsoleAppender(loggerContext, isDecorated = false)
    rootLogger.addAppender(consoleAppender)
    rootLogger.setLevel(Level.WARN)
  }

  override def configure(loggerContext: LoggerContext): Configurator.ExecutionStatus = {
    addInfo("Setting up a logback configuration")
    loggerContext.reset() // forget everything that was configured automagically
    val rootLogger = loggerContext.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME)
    val consoleAppender = mkConsoleAppender(loggerContext, isDecorated = true)
    // only warnings at the root level
    rootLogger.setLevel(Level.WARN)
    (runDir ++ customRunDir).foreach(d =>
      rootLogger.addAppender(mkFileAppender(loggerContext, d.resolve("detailed.log").toFile())))
    rootLogger.addAppender(consoleAppender)
    // debug messages at the legacy Apalache level
    val legacyApalacheLogger = loggerContext.getLogger("at.forsyte.apalache")
    legacyApalacheLogger.setLevel(Level.DEBUG)
    // debug messages at the newer Apalache level
    val newApalacheLogger = loggerContext.getLogger("com.github.apalachemc.apalache")
    newApalacheLogger.setLevel(Level.DEBUG)
    Configurator.ExecutionStatus.NEUTRAL
  }

  private def mkConsoleAppender(loggerContext: LoggerContext, isDecorated: Boolean): ConsoleAppender[ILoggingEvent] = {
    // set up ConsoleAppender
    val app = new ConsoleAppender[ILoggingEvent]()
    app.setContext(loggerContext)
    app.setName("console")
    val filter = new ThresholdFilter()
    filter.setContext(loggerContext)
    filter.setLevel(Level.INFO.levelStr)
    filter.start()
    app.addFilter(filter)
    val layout = new PatternLayout()
    layout.setPattern(if (isDecorated) "%-65msg %.-1level@%d{HH:mm:ss.SSS}%n" else "%-80msg%n")
    layout.setContext(loggerContext)
    layout.start()
    val encoder = new LayoutWrappingEncoder[ILoggingEvent]()
    encoder.setContext(loggerContext)
    encoder.setLayout(layout)
    app.setEncoder(encoder)
    app.start()
    app
  }

  private def mkFileAppender(loggerContext: LoggerContext, file: File): FileAppender[ILoggingEvent] = {
    // set up FileAppender
    val app = new FileAppender[ILoggingEvent]()
    app.setContext(loggerContext)
    app.setName("file")
    app.setFile(file.getCanonicalPath)
    val encoder = new LayoutWrappingEncoder[ILoggingEvent]()
    encoder.setContext(loggerContext)
    val layout = new PatternLayout()
    layout.setPattern("%d{\"yyyy-MM-dd'T'HH:mm:ss,SSS\"} [%thread] %-5level %logger{12} - %msg%n")
    layout.setContext(loggerContext)
    layout.start()
    encoder.setLayout(layout)
    app.setEncoder(encoder)
    val filter = new ThresholdFilter()
    filter.setLevel(Level.DEBUG.levelStr)
    filter.setContext(loggerContext)
    filter.start()
    app.addFilter(filter)
    app.start()
    app
  }
}

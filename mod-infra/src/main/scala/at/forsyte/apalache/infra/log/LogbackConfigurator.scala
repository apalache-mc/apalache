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
 * @author Igor Konnov
 */
class LogbackConfigurator(runDir: Path) extends ContextAwareBase with Configurator {
  def configureDefaultContext(): Unit = {
    val loggerContext = LoggerFactory.getILoggerFactory.asInstanceOf[LoggerContext]
    setContext(loggerContext)
    configure(loggerContext)
  }

  override def configure(loggerContext: LoggerContext): Unit = {
    addInfo("Setting up a logback configuration")
    loggerContext.reset() // forget everything that was configured automagically
    val rootLogger = loggerContext.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME)
    val consoleAppender = mkConsoleAppender(loggerContext)
    // only warnings at the root level
    rootLogger.setLevel(Level.WARN)
    rootLogger.addAppender(mkFileAppender(loggerContext))
    rootLogger.addAppender(consoleAppender)
    // debug messages at the apalache level
    val apalacheLogger = loggerContext.getLogger("at.forsyte.apalache")
    apalacheLogger.setLevel(Level.DEBUG)
  }

  private def mkConsoleAppender(loggerContext: LoggerContext): ConsoleAppender[ILoggingEvent] = {
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
    layout.setPattern("%-65msg %.-1level@%d{HH:mm:ss.SSS}%n")
    layout.setContext(loggerContext)
    layout.start()
    val encoder = new LayoutWrappingEncoder[ILoggingEvent]()
    encoder.setContext(loggerContext)
    encoder.setLayout(layout)
    app.setEncoder(encoder)
    app.start()
    app
  }

  private def mkFileAppender(loggerContext: LoggerContext): FileAppender[ILoggingEvent] = {
    // set up FileAppender
    val app = new FileAppender[ILoggingEvent]()
    app.setContext(loggerContext)
    app.setName("file")
    app.setFile(new File(runDir.toFile, "detailed.log").getCanonicalPath)
    val encoder = new LayoutWrappingEncoder[ILoggingEvent]()
    encoder.setContext(loggerContext)
    val layout = new PatternLayout()
    layout.setPattern("%d{HH:mm:ss.SSS} [%thread] %-5level %logger{12} - %msg%n")
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

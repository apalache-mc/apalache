package at.forsyte.apalache.tla.passes.imp

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, ToolModule}
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.config.{CommonOptions, ModuleIoOptions, ValidatedParseOptions}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.ParserExceptionAdapter
import com.google.inject.TypeLiteral

/**
 * A module that consists only of the parsing pass.
 *
 * @author
 *   Igor Konnov
 */
class ParserModule(options: ValidatedParseOptions, outputManager: OutputManager) extends ToolModule {
  override def configure(): Unit = {
    bind(classOf[OutputManager]).toInstance(outputManager)
    bind(classOf[CommonOptions]).toInstance(options.common)
    bind(classOf[ModuleIoOptions]).toInstance(ModuleIoOptions(options.source, options.output))

    // exception handler
    bind(classOf[ExceptionAdapter])
      .to(classOf[ParserExceptionAdapter])
    // Create an annotation store with the custom provider.
    // We have to use TypeLiteral, as otherwise Guice is getting confused by type erasure.
    bind(new TypeLiteral[AnnotationStore]() {})
      .toProvider(classOf[AnnotationStoreProvider])

    // writers
    bind(classOf[TlaWriterFactory])
      .to(classOf[PrettyWriterWithAnnotationsFactory])

    bind(classOf[SanyParserPass])
      .to(classOf[SanyParserPassImpl])
  }

  override def passes: Seq[Class[_ <: Pass]] = Seq(classOf[SanyParserPass])
}

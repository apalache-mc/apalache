package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, ToolModule, WriteablePassOptions}
import at.forsyte.apalache.io.annotations.{AnnotationStoreProvider, PrettyWriterWithAnnotationsFactory}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.ParserExceptionAdapter
import at.forsyte.apalache.io.lir.TlaWriterFactory
import com.google.inject.TypeLiteral
import at.forsyte.apalache.infra.passes.options.OptionGroup

/**
 * A module that consists only of the parsing pass.
 *
 * @author
 *   Igor Konnov
 */
class ParserModule(options: OptionGroup.HasIO) extends ToolModule(options) {
  override def configure(): Unit = {
    // Set up the sub-trait hierarchy.
    // TODO This is mad, and must be replaced.
    // See https://stackoverflow.com/questions/31598703/does-guice-binding-bind-subclass-as-well
    bind(classOf[OptionGroup]).to(classOf[OptionGroup.HasCommon])
    bind(classOf[OptionGroup.HasCommon]).to(classOf[OptionGroup.HasInput])
    bind(classOf[OptionGroup.HasInput]).to(classOf[OptionGroup.HasIO])
    bind(classOf[OptionGroup.HasOutput]).to(classOf[OptionGroup.HasIO])
    bind(classOf[OptionGroup.HasIO])
      .toInstance(options)

    // the options singleton
    bind(classOf[PassOptions])
      .to(classOf[WriteablePassOptions])
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

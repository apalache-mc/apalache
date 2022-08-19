package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import com.typesafe.scalalogging.Logger
import org.apache.commons.io.FilenameUtils

import at.forsyte.apalache.infra.passes.options.OptionGroup

object utils {
  // write output to specified destination (--output), if requested
  def writeToOutput(
      module: TlaModule,
      options: OptionGroup.HasOutput,
      writerFactory: TlaWriterFactory,
      logger: Logger,
      sourceStore: SourceStore): Unit =
    options.output.output.foreach { outfile =>
      val outfileName = outfile.toString()

      val ext = FilenameUtils.getExtension(outfileName)
      val name = FilenameUtils.getBaseName(outfileName)

      ext match {
        case "tla" =>
          writerFactory.writeModuleToTla(
              module.copy(name),
              TlaWriter.STANDARD_MODULES,
              Some(outfile),
          )
        case "json" =>
          writerFactory.writeModuleToJson(
              module.copy(name),
              TlaWriter.STANDARD_MODULES,
              Some(outfile),
          )
        case _ =>
          logger.error(s"  > Unrecognized file format: ${outfile.toString}. Supported formats: .tla and .json")
      }
      if (options.common.debug) {
        val sourceLocator =
          SourceLocator(sourceStore.makeSourceMap, new ChangeListener())
        module.operDeclarations.foreach(sourceLocator.checkConsistency)
      }
    }
}

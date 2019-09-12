package at.forsyte.apalache.tla.imp.passes

import java.io.File

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaModule
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * Parsing TLA+ code with SANY.
  *
  * @author Igor Konnov
  */

class SanyParserPassImpl @Inject()(val options: PassOptions,
                                   val sourceStore: SourceStore,
                                   @Named("AfterParser") val nextPass: Pass with TlaModuleMixin)
  extends SanyParserPass with LazyLogging {

  private var rootModule: Option[TlaModule] = None

  /**
    * The name of the pass
    *
    * @return the name associated with the pass
    */
  override def name: String = "SanyParser"

  /**
    * Run the pass
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    val filename = options.getOptionOrError("parser", "filename").asInstanceOf[String]
    val (rootName, modules) = new SanyImporter(sourceStore).loadFromFile(new File(filename))
    rootModule = modules.get(rootName)
    if (rootModule.isEmpty) {
      logger.error("Error parsing file " + filename)
    }
    rootModule.isDefined
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] =
    rootModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
}

package at.forsyte.apalache.tla.pp.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.pp.Unroller
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * An unrolling pass that
  *
  * @param options pass options
  * @param tracker transformation tracker
  * @param nextPass next pass to call
  */
class UnrollPassImpl @Inject()( val options: PassOptions,
                      tracker: TransformationTracker,
                     @Named("AfterUnroll") nextPass: Pass with TlaModuleMixin)
  extends UnrollPass with LazyLogging {

  private var outputTlaModule: Option[TlaModule] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "UnrollPass"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    val module = tlaModule.get

    val unroller = Unroller(tracker)

    logger.info("  > %s".format(unroller.getClass.getSimpleName))
    val newModule = unroller(module)

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(newModule, new File(outdir.toFile, "out-unroll.tla"))

    outputTlaModule = Some(newModule)
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    outputTlaModule map { m =>
      nextPass.setModule( m )
      nextPass
    }
  }

}

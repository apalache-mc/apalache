package at.forsyte.apalache.tla.pp.passes

import java.io.File
import java.nio.file.Path
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty}
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.{UniqueNameGenerator, Unroller}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * An unrolling pass that
 *
 * @param options  pass options
 * @param tracker  transformation tracker
 * @param nextPass next pass to call
 */
class UnrollPassImpl @Inject() (val options: PassOptions, nameGenerator: UniqueNameGenerator,
    tracker: TransformationTracker, renaming: IncrementalRenaming, writerFactory: TlaWriterFactory,
    @Named("AfterUnroll") val nextPass: Pass with TlaModuleMixin)
    extends UnrollPass with LazyLogging {

  override def name: String = "UnrollPass"

  override def execute(): Boolean = {
    val module = tlaModule.get

    // We have to rename the input, as LOCAL-toplevel TLA+ functions get
    // introduced as LET-IN operators (copying the definition). The problem is,
    // the operator bodies may introduce namespace collisions, e.g. with
    //
    // LOCAL f[x \in S] = x
    // Op(x) == f[x + 1]
    //   |
    //   V
    // Op(x) == LET f == [x \in S] In f[(x + 1)] <- namespace collision on x
    //
    val renamedModule = renaming.renameInModule(module)

    val unroller = Unroller(nameGenerator, tracker, renaming)
    logger.info("  > %s".format(unroller.getClass.getSimpleName))

    // TODO: re-enable cacher once caching is reworked (see #276 for context)
    val newModule = unroller(renamedModule)

    // dump the result of preprocessing
    writerFactory.writeModuleAllFormats(newModule.copy(name = "04_OutUnroll"), TlaWriter.STANDARD_MODULES)

    nextPass.updateModule(this, newModule)
    true
  }

  override def dependencies = Set(ModuleProperty.Desugared)

  override def transformations = Set(ModuleProperty.Unrolled)
}

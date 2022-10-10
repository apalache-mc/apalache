package at.forsyte.apalache.tla.tracee.pass

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir._
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * The implementation of a bounded model checker with SMT.
 *
 * @author
 *   Jure Kukovec
 */
class BridgingPassImpl @Inject() extends BridgingPass with LazyLogging {

  override def name: String = "BridgingPass"

  override def execute(module: TlaModule): PassResult = Right(module)

  override def dependencies = Set()

  // Required by BMC, set by a pass that isn't needed in TraceE mode.
  override def transformations = Set(ModuleProperty.Analyzed)
}

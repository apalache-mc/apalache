package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}

/**
 * <p>An analysis or transformation pass. Instead of explicitly setting a pass' input and output, we interconnect passes
 * with Google Guice and delegate the actual calls to the pass. Thus, normally, passes follow a pipeline, but they also
 * can follow an arbitrary graph.</p>
 *
 * <p>Note that the passes must be stateless, as no guarantee is provided on that the same pass is called several times.
 * When a pass finishes its job, it should set up the properties of the next pass.</p>
 *
 * <p>If you are looking for a way to store intermediate results, use a KeyValueStore.</p>
 *
 * @author
 *   Igor Konnov
 */
trait Pass {

  /**
   * The pass name.
   *
   * @return
   *   the name associated with the pass
   */
  def name: String

  var passNumber: Int = 0

  /**
   * Updates the pass number internally
   *
   * @return
   *   This pass, with an updated pass number
   */
  def withNumber(i: Int): Pass = {
    passNumber = i
    this
  }

  /**
   * Run the pass.
   * @param module
   *   The module to be transformed by the pass
   *
   * @return
   *   the transformed module, if the pass was successful
   */
  def execute(module: TlaModule): PassResult

  /**
   * List the dependencies of the pass. These are properties the module has to have in order to be processed by the
   * pass. Transitive dependencies are ignored, so if A depends on B and B depends on C The possible dependency from A
   * to C will not be declared
   *
   * @return
   *   the set of dependencies
   */
  def dependencies: Set[ModuleProperty.Value]

  /**
   * List transformations the pass applies. These are properties the module will additionally have at the end of the
   * execution
   *
   * @return
   *   the set of transformations
   */
  def transformations: Set[ModuleProperty.Value]

}

object Pass {
  type PassResult = Either[TExitCode, TlaModule]
}

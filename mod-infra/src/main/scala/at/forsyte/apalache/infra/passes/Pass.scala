package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.ModuleProperty

/**
 * <p>An analysis or transformation pass. Instead of explicitly setting
 * a pass' input and output, we interconnect passes with Google Guice and
 * delegate the actual calls to the pass. Thus, normally,
 * passes follow a pipeline, but they also can follow an arbitrary graph.</p>
 *
 * <p>Note that the passes must be stateless, as no guarantee is provided
 * on that the same pass is called several times. When a pass finishes
 * its job, it should set up the properties of the next pass.</p>
 *
 * <p>If you are looking for a way to store intermediate results, use a KeyValueStore.</p>
 *
 * @author Igor Konnov
 */
trait Pass {

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  def name: String

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  def execute(): Boolean

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass with the module trait
   */
  def nextPass: Pass with TlaModuleMixin

  /**
   * List the dependencies of the pass.
   * These are properties the module has to have in order to be processed by the pass.
   * Transitive dependencies are ignored, so if A depends on B and B depends on C
   * The possible dependency from A to C will not be declared
   *
   * @return the set of dependencies
   */
  def dependencies: Set[ModuleProperty.Value]

  /**
   * List transformations the pass applies.
   * These are properties the module will additionally have at the end of the execution
   *
   * @return the set of transformations
   */
  def transformations: Set[ModuleProperty.Value]

}

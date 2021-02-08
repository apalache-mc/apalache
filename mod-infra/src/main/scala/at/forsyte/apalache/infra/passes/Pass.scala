package at.forsyte.apalache.infra.passes

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
   * @return the next pass, if exists, or None otherwise
   */
  def next(): Option[Pass]
}

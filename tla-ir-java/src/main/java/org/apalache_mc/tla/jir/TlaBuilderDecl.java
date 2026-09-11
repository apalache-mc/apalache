package org.apalache_mc.tla.jir;

/**
 * A pending operator declaration created with {@link TlaCheckedBuilder}.
 *
 * <p>Pass it to {@code letIn} to use it in an expression, or to the builder's {@code build} method to obtain the
 * corresponding TLA+ IR declaration. Its contents are intentionally not exposed; declarations are combined and
 * validated through the builder.</p>
 */
public final class TlaBuilderDecl {
  private final Object state;

  /**
   * Creates the opaque declaration handle used by the facade implementation.
   *
   * @param state the underlying declaration computation
   */
  TlaBuilderDecl(Object state) {
    this.state = state;
  }

  /**
   * Returns the underlying declaration computation to the facade implementation.
   *
   * @return the underlying declaration computation
   */
  Object state() {
    return state;
  }
}

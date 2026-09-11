package org.apalache_mc.tla.jir;

/**
 * A pending TLA+ expression created with {@link TlaCheckedBuilder}.
 *
 * <p>Pass it to other builder methods to compose larger expressions, or to the builder's {@code build} method to obtain
 * the corresponding TLA+ IR expression. Its contents are intentionally not exposed; expressions are combined and
 * validated through the builder.</p>
 */
public final class TlaBuilderExpr {
  private final Object state;

  /**
   * Creates the opaque expression handle used by the facade implementation.
   *
   * @param state the underlying expression computation
   */
  TlaBuilderExpr(Object state) {
    this.state = state;
  }

  /**
   * Returns the underlying expression computation to the facade implementation.
   *
   * @return the underlying expression computation
   */
  Object state() {
    return state;
  }
}

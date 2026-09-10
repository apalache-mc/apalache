package org.apalache_mc.tla.jio;

/**
 * Thrown when {@link TlaJson#readModule(String)} cannot parse JSON or decode a typed TLA+ module.
 * The original parsing or decoding error is available from {@link #getCause()}.
 */
public final class TlaJsonException extends RuntimeException {
  /**
   * Creates an exception with a description and the original parsing or decoding failure.
   *
   * @param message a description of the invalid input
   * @param cause the original parsing or decoding failure
   */
  public TlaJsonException(String message, Throwable cause) {
    super(message, cause);
  }
}

package org.apalache_mc.tla.jir;

/**
 * Base exception for errors reported while constructing or validating TLA+ IR.
 *
 * <p>Catch this type to handle any error reported by the Java builders. More specific subclasses distinguish invalid
 * types from invalid name or scope usage.</p>
 */
public class TlaBuilderException extends RuntimeException {
  /**
   * Creates an exception describing why a builder operation failed.
   *
   * @param message a description of the invalid input or operation
   */
  public TlaBuilderException(String message) {
    super(message);
  }

  /**
   * Creates a builder exception that retains the original failure.
   *
   * @param message a description of the invalid builder input
   * @param cause the error that caused the builder operation to fail
   */
  public TlaBuilderException(String message, Throwable cause) {
    super(message, cause);
  }
}

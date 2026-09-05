package org.apalache_mc.tla.jir;

/**
 * Indicates that a builder operation received incompatible TLA+ types.
 *
 * <p>Examples include adding a Boolean to an integer, using a non-Boolean expression as a predicate, or applying a
 * function to an argument that does not match its parameter type. The exception message describes the expected and
 * actual types.</p>
 */
public final class TlaBuilderTypeException extends TlaBuilderException {
  /**
   * Creates an exception describing invalid operand or result types.
   *
   * @param message a description of the type mismatch
   * @param cause the error that caused type validation to fail
   */
  public TlaBuilderTypeException(String message, Throwable cause) {
    super(message, cause);
  }
}

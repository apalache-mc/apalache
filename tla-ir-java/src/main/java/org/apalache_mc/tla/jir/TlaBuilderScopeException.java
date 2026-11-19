package org.apalache_mc.tla.jir;

/**
 * Indicates that {@link TlaCheckedBuilder} found an invalid use of a name.
 *
 * <p>Examples include reusing a name with an incompatible type, referring to a name whose type cannot be inferred, or
 * shadowing a bound variable or local operator. The exception message identifies the offending name and context.</p>
 */
public final class TlaBuilderScopeException extends TlaBuilderException {
  /**
   * Creates an exception describing invalid name or scope usage.
   *
   * @param message a description of the invalid name usage
   * @param cause the error that caused scope validation to fail
   */
  public TlaBuilderScopeException(String message, Throwable cause) {
    super(message, cause);
  }
}

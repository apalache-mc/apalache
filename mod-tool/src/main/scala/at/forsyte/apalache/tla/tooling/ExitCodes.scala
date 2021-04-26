package at.forsyte.apalache.tla.tooling

import tlc2.output.EC

/**
 * Exit codes that are reported by Tool. In contrast, we are using a small subset of exit codes.
 * Although we maintain exit codes that are compatible with TLC, we believe that exit codes should not
 * replace richer error explanations.
 *
 * @author Igor Konnov
 */
object ExitCodes {

  /**
   * This exit code should be used when the tool is reporting no error in a specification.
   */
  val NO_ERROR: Int = EC.ExitStatus.SUCCESS

  /**
   * This exit code should be used when the model checker has found a counterexample.
   * We do not go in distinction between different kinds of counterexamples and always report VIOLATION_SAFETY.
   */
  val ERROR_COUNTEREXAMPLE: Int = EC.ExitStatus.VIOLATION_SAFETY

  /**
   * This exit code should be used for other kinds of errors, e.g., configuration errors, type errors, runtime errors.
   */
  val ERROR: Int = EC.ExitStatus.ERROR
}

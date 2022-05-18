package at.forsyte.apalache.infra

import tlc2.output.EC

/**
 * Exit codes that are reported by `Tool`.
 *
 * We maintain compatibility with TLC on a small subset of its exit codes, believing that exit codes should not replace
 * richer error explanations.
 *
 * TLC currently specifies exit codes
 *   - 0 for success,
 *   - 10–14 for (various kinds of) property violations,
 *   - 75–77 for "failures" (e.g., properties that are tautologies, or primed variables in invariants), and
 *   - 150–153 and 255 for syntax errors and system-level errors, respectively.
 *
 * Apalache uses exit codes
 *   - 0 for success,
 *   - 12 for all kinds of property violations,
 *   - 75 for semantic failures to evaluate a specification,
 *   - 120 for type-checking errors,
 *   - 150 for syntactic errors, and
 *   - 255 for general system-level errors.
 *
 * @author
 *   Igor Konnov, Thomas Pani
 */
object ExitCodes {
  type TExitCode = Int

  /**
   * No error in the specification.
   */
  val OK: TExitCode = EC.ExitStatus.SUCCESS // = 0

  /**
   * The model checker has found a counterexample. We do not distinguish between different kinds of counterexamples and
   * always report VIOLATION_SAFETY.
   */
  val ERROR_COUNTEREXAMPLE: TExitCode = EC.ExitStatus.VIOLATION_SAFETY // = 12

  /**
   * Semantic failure to evaluate a specification, e.g. due to unsupported language constructs and operators, or those
   * that introduce infinite structures.
   */
  val FAILURE_SPEC_EVAL: TExitCode = EC.ExitStatus.FAILURE_SPEC_EVAL // = 75

  /**
   * Type-checking error.
   */
  val ERROR_TYPECHECK: TExitCode = 120

  /**
   * Syntactic error when parsing the spec.
   */
  val ERROR_SPEC_PARSE: TExitCode = EC.ExitStatus.ERROR_SPEC_PARSE // = 150

  /**
   * All other kinds of errors, e.g., runtime errors.
   */
  val ERROR: TExitCode = EC.ExitStatus.ERROR // 255
}

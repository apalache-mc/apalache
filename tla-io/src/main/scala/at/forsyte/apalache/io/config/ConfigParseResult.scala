package at.forsyte.apalache.io.config

/**
 * The result of reading or resolving configuration.
 *
 * Expected user errors are values, not exceptions. A successful result has a value and no errors. Warnings may be
 * present in either successful or unsuccessful results.
 */
final case class ConfigParseResult[A](
    value: Option[A],
    errors: List[String] = Nil,
    warnings: List[String] = Nil) {

  def isSuccess: Boolean = value.nonEmpty && errors.isEmpty

  /**
   * Return the value after [[isSuccess]] has been checked.
   *
   * This throws only when the caller violates the ConfigParseResult contract; configuration failures themselves are
   * stored in [[errors]].
   */
  def requireValue(): A = {
    if (!isSuccess) {
      throw new IllegalStateException("Configuration parse result has no value")
    }
    value.get
  }
}

object ConfigParseResult {

  def success[A](value: A, warnings: List[String] = Nil): ConfigParseResult[A] =
    ConfigParseResult(Some(value), warnings = warnings)

  def failure[A](error: String): ConfigParseResult[A] =
    ConfigParseResult(None, errors = List(error))

  def failure[A](errors: List[String], warnings: List[String] = Nil): ConfigParseResult[A] =
    ConfigParseResult(None, errors, warnings)

  def failureFrom[A, B](result: ConfigParseResult[B]): ConfigParseResult[A] =
    failure(result.errors, result.warnings)

  def withWarnings[A](result: ConfigParseResult[A], extraWarnings: List[String]): ConfigParseResult[A] =
    result.copy(warnings = result.warnings ++ extraWarnings)
}

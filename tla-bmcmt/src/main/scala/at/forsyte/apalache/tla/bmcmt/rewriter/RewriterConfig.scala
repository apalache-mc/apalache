package at.forsyte.apalache.tla.bmcmt.rewriter

/**
 * Configuration options for SymbStateRewriter, see tuning.md.
 *
 * @author
 *   Igor Konnov
 */
class RewriterConfig {

  /**
   * If true, translate 'or' and 'and' into 'if-then-else'.
   */
  var shortCircuit = true
}

object RewriterConfig {

  /**
   * Construct config from a map of string, e.g., produced by tuning.properties
   * @param options
   *   a map of strings
   * @return
   *   a new config
   */
  def apply(options: Map[String, String]): RewriterConfig = {
    val config = new RewriterConfig
    config.shortCircuit = options.getOrElse("rewriter.shortCircuit", "").toLowerCase == "true"
    config
  }
}

package at.forsyte.apalache.tla.bmcmt.rewriter

/**
  * Configuration options for SymbStateRewriter, see tuning.md.
  *
  * @author Igor Konnov
  */
class RewriterConfig {
  /**
    * If true, translate 'or' and 'and' into 'if-then-else'.
    */
  var shortCircuit = true
  /**
    * If true, for A /\ B, check satisfiability of A with SMT and only if it is true, rewrite B.
    */
  var lazyCircuit = false
}

object RewriterConfig {
  /**
    * Construct config from a map of string, e.g., produced by tuning.properties
    * @param options a map of strings
    * @return a new config
    */
  def apply(options: Map[String, String]): RewriterConfig = {
    val config = new RewriterConfig
    config.shortCircuit = options.getOrElse("rewriter.shortCircuit", "").toLowerCase == "true"
    config.lazyCircuit = options.getOrElse("rewriter.lazyCircuit", "").toLowerCase == "true"
    config
  }
}
package at.forsyte.apalache.io.typecheck.parser

/**
 * A factory of type parsers. For the moment being, it creates only the parser for Type System 1.
 * In the future, it may produce parsers for other type systems. For simplicity, it is a singleton,
 * but this may change in the future.
 *
 * @author Igor Konnov
 */
object TypeParserFactory {

  /**
   * Create a parser for type system 1.
   *
   * @return a parser instance
   */
  def type1Parser(): Type1Parser = {
    DefaultType1Parser
  }
}

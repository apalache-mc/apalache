package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.TlaType1

/**
 * A trait for a parser of TS1 types in the grammar of ADR-002:
 *
 * <pre>
 * T ::= typeConst | typeVar | Bool | Int | Str | T -&gt; T | Set(T) | Seq(T) |
 * &lt;&lt;T, ..., T&gt;&gt; | [h_1: T, ..., h_k: T] | (T, ..., T) =&gt; T | (T)
 * typeConst ::= &lt;an identifier that matches [A-Z_][A-Z0-9_]*&gt;
 * typeVar ::= &lt;a single letter from [a-z]&gt;
 * </pre>
 *
 * @see at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
 * @author Igor Konnov, 2020
 */
trait Type1Parser {
  type AliasMap = Map[String, TlaType1]

  /**
   * Parse a type from a string.
   *
   * @param text a string
   * @return a type on success; throws TlcConfigParseError on failure
   */
  def apply(text: String): TlaType1 = {
    parseType(Map.empty, text)
  }

  /**
   * Parse a type from a string, possibly substituting aliases with types.
   *
   * @param aliases a map of aliases to types
   * @param text    a string
   * @return a type on success; throws TlcConfigParseError on failure
   */
  def parseType(aliases: AliasMap, text: String): TlaType1

  /**
   * Parse a type alias from a string
   *
   * @param aliases a map of aliases to types
   * @param text    a string
   * @return an alias name and a type on success; throws Type1ParseError on failure
   */
  def parseAlias(aliases: AliasMap, text: String): (String, TlaType1)
}

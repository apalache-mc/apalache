package at.forsyte.apalache.tla.typecheck

/**
  * A trait for a parser of TS1 types in the grammar of ADR-002:
  *
<pre>
   T ::= typeConst | typeVar | Bool | Int | Str | T -&gt; T | Set(T) | Seq(T) |
         &lt;&lt;T, ..., T&gt;&gt; | [h_1: T, ..., h_k: T] | (T, ..., T) =&gt; T | (T)
   typeConst ::= &lt;an identifier that matches [A-Z_][A-Z0-9_]*&gt;
   typeVar ::= &lt;a single letter from [a-z]&gt;
</pre>
  *
  * @see at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
  *
  * @author Igor Konnov, 2020
  */
trait Type1Parser {

  /**
    * Parse a type from a string.
    *
    * @param text a string
    * @return a type on success; throws TlcConfigParseError on failure
    */
  def apply(text: String): TlaType1
}

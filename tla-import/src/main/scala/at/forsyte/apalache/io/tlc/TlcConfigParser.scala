package at.forsyte.apalache.io.tlc

import java.io.Reader

import at.forsyte.apalache.io.tlc.config.TlcConfig

/**
 * A trait to a parser of TLC configuration files. For the syntax,
 * see [<a href="http://research.microsoft.com/users/lamport/tla/book.html">Specifying Systems</a>, Ch. 14]
 * by Leslie Lamport. TLC configuration files have a rich assignment syntax, e.g.,
 * one can write a parameter assignment. The syntax supported by Apalache is described in
 * [<a href="https://apalache.informal.systems/docs/apalache/tlc-config.html">tlc-config</a>].
 *
 * @author Igor Konnov
 */
trait TlcConfigParser {
  def apply(reader: Reader): TlcConfig
}

package at.forsyte.apalache.io.tlc.config

import scala.util.parsing.input.Position

/**
 * The exception thrown by TlcConfigParser if any error occurs.
 *
 * @param msg the error message
 * @param pos a position in the input
 */
class TlcConfigParseError(val msg: String, val pos: Position) extends Exception(msg) {
  override def toString: String = {
    "Config parse error at %s: %s".format(pos, msg)
  }
}

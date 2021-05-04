package at.forsyte.apalache.io.tlc.config

import scala.util.parsing.input.Positional

/**
 * A token.
 */
sealed trait TlcConfigToken extends Positional

/**
 * An identifier
 * @param name the name associated with the identifier
 */
case class IDENT(name: String) extends TlcConfigToken {
  override def toString: String = "identifier '%s'".format(name)
}

/**
 * A string according to the TLA+ syntax.
 *
 * @param name the name associated with the identifier
 */
case class STRING(name: String) extends TlcConfigToken {
  override def toString: String = "string \"%s\"".format(name)
}

/**
 * A number
 * @param value the value of the number
 */
case class NUMBER(value: String) extends TlcConfigToken {
  override def toString: String = "number '%s'".format(value)
}

/**
 * A Boolean value, FALSE or TRUE.
 * @param value string representation of a Boolean value: "FALSE" or "TRUE"
 */
case class BOOLEAN(value: String) extends TlcConfigToken {
  override def toString: String = "boolean '%s'".format(value)
}

/**
 * The CONSTANT keyword.
 */
case class CONST() extends TlcConfigToken {
  override def toString: String = "CONSTANT"
}

/**
 * The INIT keyword.
 */
case class INIT() extends TlcConfigToken {
  override def toString: String = "INIT"
}

/**
 * The NEXT keyword.
 */
case class NEXT() extends TlcConfigToken {
  override def toString: String = "NEXT"
}

/**
 * The SPECIFICATION keyword.
 */
case class SPECIFICATION() extends TlcConfigToken {
  override def toString: String = "SPECIFICATION"
}

/**
 * The INVARIANT keyword.
 */
case class INVARIANT() extends TlcConfigToken {
  override def toString: String = "INVARIANT"
}

/**
 * The PROPERTY keyword.
 */
case class PROPERTY() extends TlcConfigToken {
  override def toString: String = "PROPERTY"
}

/**
 * The CONSTRAINT keyword (for state constraints).
 */
case class CONSTRAINT() extends TlcConfigToken {
  override def toString: String = "CONSTRAINT"
}

/**
 * The ACTION_CONSTRAINT keyword (for action constraints).
 */
case class ACTION_CONSTRAINT() extends TlcConfigToken {
  override def toString: String = "ACTION_CONSTRAINT"
}

/**
 * A hint about using symmetry.
 */
case class SYMMETRY() extends TlcConfigToken {
  override def toString: String = "SYMMETRY"
}

/**
 * A hint on view abstraction.
 */
case class VIEW() extends TlcConfigToken {
  override def toString: String = "VIEW"
}

/**
 * Additional output in counterexamples.
 */
case class ALIAS() extends TlcConfigToken {
  override def toString: String = "ALIAS"
}

/**
 * Postcondition to check when the model checker has terminated.
 */
case class POSTCONDITION() extends TlcConfigToken {
  override def toString: String = "POSTCONDITION"
}

/**
 * Whether the tools should check for the deadlocks.
 */
case class CHECK_DEADLOCK() extends TlcConfigToken {
  override def toString: String = "CHECK_DEADLOCK"
}

/**
 * An assignment "<-".
 */
case class LEFT_ARROW() extends TlcConfigToken {
  override def toString: String = "<-"
}

/**
 * An equality "=".
 */
case class EQ() extends TlcConfigToken {
  override def toString: String = "="
}

/**
 * Left brace "{".
 */
case class LEFT_BRACE() extends TlcConfigToken {
  override def toString: String = "{"
}

/**
 * Right brace "}".
 */
case class RIGHT_BRACE() extends TlcConfigToken {
  override def toString: String = "}"
}

/**
 * Comma ",".
 */
case class COMMA() extends TlcConfigToken {
  override def toString: String = ","
}

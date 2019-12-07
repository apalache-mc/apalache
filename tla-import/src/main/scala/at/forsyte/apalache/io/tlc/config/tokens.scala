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
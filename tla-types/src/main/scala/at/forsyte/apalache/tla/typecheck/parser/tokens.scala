package at.forsyte.apalache.tla.typecheck.parser

import scala.util.parsing.input.Positional

/**
  * A token.
  */
private[parser] sealed trait Type1Token extends Positional

/**
  * A capitalized identifier
  * @param name the name associated with the identifier
  */
private[parser] case class CAPS_IDENT(name: String) extends Type1Token {
  override def toString: String = "CAPS ident '%s'".format(name)
}

/**
  * A field identifier. Since it syntactically includes CAPS_IDENT and LETTER_IDENT, one has to expect
  * CAPS_IDENT, LETTER_INDENT, and FIELD_INDENT, whenever a record field is expected.
  *
  * @param name the name associated with the field
  */
private[parser] case class FIELD_IDENT(name: String) extends Type1Token {
  override def toString: String = "record field '%s'".format(name)
}

/**
  * An integer identifier: Int
  */
private[parser] case class INT() extends Type1Token {
  override def toString: String = "Int"
}

/**
  * A real identifier: Real
  */
private[parser] case class REAL() extends Type1Token {
  override def toString: String = "Real"
}

/**
  * A string identifier: Str
  */
private[parser] case class STR() extends Type1Token {
  override def toString: String = "Str"
}

/**
  * A Boolean identifier: Bool
  */
private[parser] case class BOOL() extends Type1Token {
  override def toString: String = "Bool"
}

/**
  * Name of the set constructor.
  */
private[parser] case class SET() extends Type1Token {
  override def toString: String = "Set"
}

/**
  * Name of the sequence constructor.
  */
private[parser] case class SEQ() extends Type1Token {
  override def toString: String = "Seq"
}

/**
  * A right arrow "->".
  */
private[parser] case class RIGHT_ARROW() extends Type1Token {
  override def toString: String = "->"
}

/**
  * A right arrow "=>".
  */
private[parser] case class DOUBLE_RIGHT_ARROW() extends Type1Token {
  override def toString: String = "=>"
}

/**
  * A comma.
  */
private[parser] case class COMMA() extends Type1Token {
  override def toString: String = ","
}

/**
  * A colon.
  */
private[parser] case class COLON() extends Type1Token {
  override def toString: String = ":"
}

/**
  * Left parenthesis "(".
  */
private[parser] case class LPAREN() extends Type1Token {
  override def toString: String = "("
}

/**
  * Right parenthesis ")".
  */
private[parser] case class RPAREN() extends Type1Token {
  override def toString: String = ")"
}

/**
  * Left bracket "[".
  */
private[parser] case class LBRACKET() extends Type1Token {
  override def toString: String = "["
}

/**
  * Right bracket "]".
  */
private[parser] case class RBRACKET() extends Type1Token {
  override def toString: String = "]"
}

/**
  * Left curly bracket "{".
  */
private[parser] case class LCURLY() extends Type1Token {
  override def toString: String = "{"
}

/**
  * Right curly bracket "}".
  */
private[parser] case class RCURLY() extends Type1Token {
  override def toString: String = "}"
}

/**
  * A field number, e.g., 3
  * @param no the number
  */
private[parser] case class FIELD_NO(no: Int) extends Type1Token {
  override def toString: String = no.toString
}

/**
  * Tuple opening "<<".
  */
private[parser] case class DOUBLE_LEFT_ANGLE() extends Type1Token {
  override def toString: String = "<<"
}

/**
  * Tuple opening ">>".
  */
private[parser] case class DOUBLE_RIGHT_ANGLE() extends Type1Token {
  override def toString: String = ">>"
}
package at.forsyte.apalache.tla.types.parser

import scala.util.parsing.input.Positional

/**
 * A token.
 */
sealed private[parser] trait Type1Token extends Positional

/**
 * A field identifier. Since it syntactically includes CAPS_IDENT and LETTER_IDENT, one has to expect CAPS_IDENT,
 * LETTER_INDENT, and FIELD_INDENT, whenever a record field is expected.
 *
 * @param name
 *   the name associated with the field
 */
private[parser] case class IDENT(name: String) extends Type1Token {
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
 * Name of the variant constructor (when a row is passed directly).
 */
private[parser] case class VARIANT() extends Type1Token {
  override def toString: String = "Variant"
}

/**
 * Name of the record constructor (when a row is passed directly).
 */
private[parser] case class RECORD() extends Type1Token {
  override def toString: String = "Rec"
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
 * Equality sign "=" (used by the alias definition).
 */
private[parser] case class EQ() extends Type1Token {
  override def toString: String = "="
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
 * The dollar sign.
 */
private[parser] case class DOLLAR() extends Type1Token {
  override def toString: String = "$"
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
 *
 * @param no
 *   the number
 */
private[parser] case class FIELD_NO(no: Int) extends Type1Token {
  override def toString: String = no.toString
}

/**
 * A string literal, e.g., "hello".
 *
 * @param text
 *   the string contents
 */
private[parser] case class STR_LITERAL(text: String) extends Type1Token {
  override def toString: String = s"\"${text}\""
}

/**
 * Tuple opening "<<".
 */
private[parser] case class DOUBLE_LEFT_ANGLE() extends Type1Token {
  override def toString: String = "<<"
}

/**
 * Tuple closing ">>".
 */
private[parser] case class DOUBLE_RIGHT_ANGLE() extends Type1Token {
  override def toString: String = ">>"
}

/**
 * Pipe "|".
 */
private[parser] case class PIPE() extends Type1Token {
  override def toString: String = "|"
}

/**
 * Opening a row "(|".
 */
private[parser] case class LROW() extends Type1Token {
  override def toString: String = "(|"
}

/**
 * Closing a row "|)".
 */
private[parser] case class RROW() extends Type1Token {
  override def toString: String = "|)"
}

/**
 * Opening a sparse tuple "<|".
 */
private[parser] case class LTUPLE_ROW() extends Type1Token {
  override def toString: String = "<|"
}

/**
 * Closing a sparse tuple "|>".
 */
private[parser] case class RTUPLE_ROW() extends Type1Token {
  override def toString: String = "|>"
}

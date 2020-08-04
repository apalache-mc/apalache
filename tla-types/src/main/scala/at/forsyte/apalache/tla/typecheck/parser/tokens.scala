package at.forsyte.apalache.tla.typecheck.parser

import scala.util.parsing.input.Positional

/**
  * A token.
  */
sealed trait Type1Token extends Positional

/**
  * A capitalized identifier
  * @param name the name associated with the identifier
  */
case class CAPS_IDENT(name: String) extends Type1Token {
  override def toString: String = "CAPS ident '%s'".format(name)
}

/**
  * A single-letter identifier. For consistency with CAPS_INDENT, we assign a String to name, not Char.
  *
  * @param name the name associated with the identifier
  */
case class LETTER_IDENT(name: String) extends Type1Token {
  require(name.length == 1)

  override def toString: String = "letter ident '%s'".format(name)
}

/**
  * An integer identifier: Int
  */
case class INT() extends Type1Token {
  override def toString: String = "Int"
}

/**
  * A string identifier: Str
  */
case class STR() extends Type1Token {
  override def toString: String = "Str"
}

/**
  * A Boolean identifier: Bool
  */
case class BOOL() extends Type1Token {
  override def toString: String = "Bool"
}

/**
  * Name of the set constructor.
  */
case class SET() extends Type1Token {
  override def toString: String = "Set"
}

/**
  * Name of the sequence constructor.
  */
case class SEQ() extends Type1Token {
  override def toString: String = "Seq"
}

/**
  * A right arrow "->".
  */
case class RIGHT_ARROW() extends Type1Token {
  override def toString: String = "->"
}

/**
  * A right arrow "=>".
  */
case class DOUBLE_RIGHT_ARROW() extends Type1Token {
  override def toString: String = "=>"
}

/**
  * Left parenthesis "(".
  */
case class LPAREN() extends Type1Token {
  override def toString: String = "("
}

/**
  * Right parenthesis ")".
  */
case class RPAREN() extends Type1Token {
  override def toString: String = ")"
}

/**
  * Tuple opening "<<".
  */
case class DOUBLE_LEFT_ANGLE() extends Type1Token {
  override def toString: String = "<<"
}

/**
  * Tuple opening ">>".
  */
case class DOUBLE_RIGHT_ANGLE() extends Type1Token {
  override def toString: String = ">>"
}
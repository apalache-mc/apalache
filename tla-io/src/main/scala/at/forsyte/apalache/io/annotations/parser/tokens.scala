package at.forsyte.apalache.io.annotations.parser

import scala.util.parsing.input.Positional

/**
 * A token that can be used in annotation.
 */
sealed trait AnnotationToken extends Positional

/**
 * Arbitrary text that could be used outside of an annotation.
 * The lexer may produce such tokens internally, but it never gives them to the API user.
 */
case class JUNK() extends AnnotationToken {}

/**
 * An identifier
 *
 * @param name the name associated with the identifier
 */
case class IDENT(name: String) extends AnnotationToken {}

/**
 * Annotation name that start with "@". We introduce a special token for that instead of using
 * a token for "@" and IDENT. The reason is that we want to ignore standalone "@" in the parser.
 * See: https://github.com/informalsystems/apalache/issues/757
 *
 * @param name the name associated with the identifier
 */
case class AT_IDENT(name: String) extends AnnotationToken {}

/**
 * A string according to the TLA+ syntax, that is a sequence of characters between quotes, "...".
 *
 * @param text the contents of the string
 */
case class STRING(text: String) extends AnnotationToken {}

/**
 * A string that appears between ":" and ";".
 *
 * @param text the contents of the string
 */
case class INLINE_STRING(text: String) extends AnnotationToken {}

/**
 * A number
 *
 * @param num the value of the number
 */
case class NUMBER(num: BigInt) extends AnnotationToken {}

/**
 * A Boolean value, FALSE or TRUE.
 *
 * @param bool string representation of a Boolean value: "FALSE" or "TRUE"
 */
case class BOOLEAN(bool: Boolean) extends AnnotationToken {}

/**
 * Comma ",".
 */
case class COMMA() extends AnnotationToken {}

/**
 * Dot ".". We don't really use dots, but they are useful, e.g., for parsing 1.23.
 */
case class DOT() extends AnnotationToken {}

/**
 * Left parenthesis "(".
 */
case class LPAREN() extends AnnotationToken {}

/**
 * Right parenthesis ")".
 */
case class RPAREN() extends AnnotationToken {}

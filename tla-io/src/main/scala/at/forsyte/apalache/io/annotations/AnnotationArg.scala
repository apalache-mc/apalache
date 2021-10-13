package at.forsyte.apalache.io.annotations

/**
 * An argument to an annotation.
 */
sealed abstract class AnnotationArg {}

object AnnotationArg {
  def mkStr(text: String): AnnotationArg = {
    AnnotationStr(text)
  }

  def mkIdent(name: String): AnnotationArg = {
    AnnotationIdent(name)
  }

  def mkInt(i: Int): AnnotationInt = {
    AnnotationInt(i)
  }

  def mkBool(b: Boolean): AnnotationBool = {
    AnnotationBool(b)
  }
}

/**
 * A string argument.
 *
 * @param text the text of the string argument.
 */
case class AnnotationStr(text: String) extends AnnotationArg {
  override def toString: String = '"' + text + '"'
}

/**
 * An identifier argument.
 *
 * @param name the name of an identifier.
 */
case class AnnotationIdent(name: String) extends AnnotationArg {
  override def toString: String = name
}

/**
 * An integer argument.
 *
 * @param num the value of the argument.
 */
case class AnnotationInt(num: BigInt) extends AnnotationArg {
  override def toString: String = num.toString
}

/**
 * A Boolean argument
 *
 * @param b the Boolean value of the argument.
 */
case class AnnotationBool(b: Boolean) extends AnnotationArg {
  override def toString: String = b.toString
}

package at.forsyte.apalache.io.annotations

/**
 * An argument to an annotation.
 */
sealed abstract class TlaAnnotationArg {}

object TlaAnnotationArg {
  def mkStr(text: String): TlaAnnotationArg = {
    TlaAnnotationString(text)
  }

  def mkInt(i: Int): TlaAnnotationInt = {
    TlaAnnotationInt(i)
  }

  def mkBool(b: Boolean): TlaAnnotationBool = {
    TlaAnnotationBool(b)
  }
}

/**
 * A string argument.
 * @param text the text of the string argument.
 */
case class TlaAnnotationString(text: String) extends TlaAnnotationArg {
  override def toString: String = '"' + text + '"'
}

/**
 * An integer argument.
 * @param num the value of the argument.
 */
case class TlaAnnotationInt(num: Int) extends TlaAnnotationArg {
  override def toString: String = num.toString
}

/**
 * A Boolean argument
 * @param b the Boolean value of the argument.
 */
case class TlaAnnotationBool(b: Boolean) extends TlaAnnotationArg {
  override def toString: String = b.toString
}


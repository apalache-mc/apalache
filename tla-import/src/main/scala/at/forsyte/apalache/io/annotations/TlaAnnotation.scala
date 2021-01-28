package at.forsyte.apalache.io.annotations

/**
 * <p>A Java-like annotation that is written in front of an operator declaration. For example:</p>
 *
 * <pre>
 *   \* @pure
 *   \* @type("(Int, Int) => Int")
 *   Plus(x, y) == x + y
 * </pre>
 */
class TlaAnnotation(val name: String, val args: TlaAnnotationArg*) {

  /**
   * <p>A string representation of the annotation. There are two cases:</p>
   *
   * <ol>
   *   <li>The annotation `name` has zero arguments. The output is `@name`</li>
   *   <li>The annotation `name` has N > 0 arguments `arg1`, ..., `argN`.
   *       The output is `@name(arg1, ..., argN)`</li>
   * </ol>
   *
   * @return the string representation of the annotation.
   */
  override def toString: String = {
    if (args.isEmpty) {
      "@" + name
    } else {
      val argsStr = args.mkString(", ")
      s"@$name($argsStr)"
    }
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[TlaAnnotation]

  override def equals(other: Any): Boolean = other match {
    case that: TlaAnnotation =>
      (that canEqual this) &&
        name == that.name &&
        args == that.args
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(name, args)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

object TlaAnnotation {

  /**
   * A convenient constructor for TLA+ annotations.
   * @param name annotation name, a valid Java identifier
   * @param args a list of arguments
   * @return a new annotation
   */
  def apply(name: String, args: TlaAnnotationArg*): TlaAnnotation = {
    new TlaAnnotation(name, args: _*)
  }
}

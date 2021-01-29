package at.forsyte.apalache.io.annotations

/**
 * <p>A Java-like annotation that is written in front of an operator declaration. For example:</p>
 *
 * <pre>
 * \* @pure
 * \* @type("(Int, Int) => Int")
 * Plus(x, y) == x + y
 * </pre>
 */
class Annotation(val name: String, val args: AnnotationArg*) {

  /**
   * <p>A string representation of the annotation. There are two cases:</p>
   *
   * <ol>
   * <li>The annotation `name` has zero arguments. The output is `@name`</li>
   * <li>The annotation `name` has N > 0 arguments `arg1`, ..., `argN`.
   * The output is `@name(arg1, ..., argN)`</li>
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

  /**
   * A pretty string representation. When the number of arguments is different from one, it behaves as #toString.
   * When there is one argument, it prints an annotation in the format: `@name: arg ;`
   * @return
   */
  def toPrettyString: String = {
    if (args.length != 1) {
      this.toString
    } else {
      "@%s: %s;".format(name, args.head)
    }
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[Annotation]

  override def equals(other: Any): Boolean = other match {
    case that: Annotation =>
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

object Annotation {

  /**
   * A convenient constructor for TLA+ annotations.
   *
   * @param name annotation name, a valid Java identifier
   * @param args a list of arguments
   * @return a new annotation
   */
  def apply(name: String, args: AnnotationArg*): Annotation = {
    new Annotation(name, args: _*)
  }
}

package at.forsyte.apalache.io.annotations

/**
 * <p>A Java-like annotation that is written in front of an operator declaration. For example:</p>
 *
 * <pre>
 * \* @pure
 * \* @type("(Int, Int) => Int")
 * Plus(x, y) == x + y
 * </pre>
 *
 * <p>We declare this class to be case class to make pattern matching possible.</p>
 */
case class Annotation(name: String, args: AnnotationArg*) {

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
}

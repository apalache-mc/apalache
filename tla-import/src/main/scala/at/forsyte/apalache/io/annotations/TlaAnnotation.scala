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

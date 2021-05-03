package at.forsyte.apalache.io.annotations

/**
 * This trait collects the name of the standard annotations. In case we want to change them later.
 */
object StandardAnnotations {

  /**
   * Type annotation. It should have a single string argument.
   */
  val TYPE: String = "type"

  /**
   * A type alias. It should have a single string argument.
   */
  val TYPE_ALIAS: String = "typeAlias"

  /**
   * Construct a type annotation.
   *
   * @param typeText the text of the type annotation
   * @return
   */
  def mkType(typeText: String): Annotation = {
    Annotation(TYPE, AnnotationStr(typeText))
  }

  /**
   * Construct a type alias annotation.
   *
   * @param typeText the text of the type annotation
   * @return
   */
  def mkTypeAlias(typeText: String): Annotation = {
    Annotation(TYPE_ALIAS, AnnotationStr(typeText))
  }
}

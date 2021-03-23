package at.forsyte.apalache.tla.lir

/**
 * A type tag to be attached to a TLA+ language construct: an expression or a declaration.
 */
sealed abstract class TypeTag

/**
 * The type tag that simply indicates that the language construct is not typed.
 */
case class Untyped() extends TypeTag

/**
 * A type tag that carries a tag of type T, which the tag is parameterized with.
 *
 * @param myType the type that is carried by the tag
 * @tparam T the type of the tag
 */
case class Typed[T](myType: T) extends TypeTag

/**
 * This trait defines the standard behavior of constructs that carry type tags.
 *
 * @tparam T type of the tagged object
 */
trait TypeTagged[T] {

  /**
   * A type tag of an object, e.g., of an expression or declaration.
   */
  val typeTag: TypeTag

  /**
   * Make a shallow copy of the object and set its type tag to a new value.
   *
   * @param newTypeTag a new type
   * @return a shallow copy of TLA+ expression with the type tag set to newTypeTag
   */
  def withTag(newTypeTag: TypeTag): T

  /**
   * Object equality combined with type tag equality.
   *
   * @param other another object to compare with
   * @return true, if `this == other && this.typeTag == other.typeTag`
   */
  def eqTyped(other: TypeTagged[T]): Boolean = {
    this == other && typeTag == other.typeTag
  }
}

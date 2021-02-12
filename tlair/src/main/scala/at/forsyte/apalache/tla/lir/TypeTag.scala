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
 * Default settings for the untyped language layer. To use the `Untyped()` tag, import the definitions from `UntypedPredefs`.
 */
object UntypedPredefs {
  implicit val untyped: TypeTag = Untyped()
}

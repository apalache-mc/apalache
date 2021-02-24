package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{FixedArity, OperArity}

/**
 * Convenient shortcuts and definitions, mostly used in tests. Import them, when needed.
 */
package object convenience {

  /**
   * This is just a short-hand to Builder, so one can type more naturally, e.g., tla.plus(tla.int(2), tla.int(3))
   */
  val tla: Builder.type = Builder

  implicit def makeUID(id: Int): UID = UID(id)

  implicit def opArity(n: Int): OperArity = FixedArity(n)

  trait TypeTaggedWithShortcuts[T] {

    /**
     * Produce a copy of the object with the type tag set to Untyped()
     *
     * @return a copy with the Untyped() tag
     */
    def asUntyped: T

    /**
     * Produce a copy of the object with the type tag set to Typed(tt)
     *
     * @param tt new type
     * @return a copy with Typed(tt)
     */
    def asTyped[TypeT](tt: TypeT): T
  }

  implicit def typeTaggedToShortcuts[T](tagged: TypeTagged[T]): TypeTaggedWithShortcuts[T] = {
    new TypeTaggedWithShortcuts[T] {

      /**
       * Produce a copy of the object with the type tag set to Untyped()
       *
       * @return a copy with the Untyped() tag
       */
      override def asUntyped: T = tagged.withType(Untyped())

      /**
       * Produce a copy of the object with the type tag set to Typed(tt)
       *
       * @param tt new type
       * @return a copy with Typed(tt)
       */
      override def asTyped[TypeT](tt: TypeT): T = tagged.withType(Typed(tt))
    }
  }
}

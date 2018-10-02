package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.NameEx

/**
  * Implicit conversions between cells and TLA+ expressions. Use carefully.
  */
package object implicitConversions {

  import scala.language.implicitConversions

  implicit def cell2NameEx(c: ArenaCell): NameEx = {
    c.toNameEx
  }

  implicit class Crossable[X](xs: Traversable[X]) {
    // see https://stackoverflow.com/questions/14740199/cross-product-in-scala
    def cross[Y](ys: Traversable[Y]) = for {x <- xs; y <- ys} yield (x, y)
  }
}
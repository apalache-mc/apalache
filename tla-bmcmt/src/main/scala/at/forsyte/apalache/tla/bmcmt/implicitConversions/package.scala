package at.forsyte.apalache.tla.bmcmt

/**
 * Implicit conversions between cells and TLA+ expressions. Use carefully.
 */
package object implicitConversions {

  implicit class Crossable[X](xs: Iterable[X]) {
    // see https://stackoverflow.com/questions/14740199/cross-product-in-scala
    def cross[Y](ys: Iterable[Y]) = for { x <- xs; y <- ys } yield (x, y)
  }
}

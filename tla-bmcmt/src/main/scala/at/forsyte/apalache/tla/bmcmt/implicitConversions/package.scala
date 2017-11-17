package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.NameEx

/**
  * Implicit conversions between cells and TLA+ expressions. Use carefully.
  */
package object implicitConversions {
  implicit def cell2NameEx(c: ArenaCell): NameEx = {
    c.toNameEx
  }
}
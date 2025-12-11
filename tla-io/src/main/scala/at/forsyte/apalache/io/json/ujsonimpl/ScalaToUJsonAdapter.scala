package at.forsyte.apalache.io.json.ujsonimpl

import at.forsyte.apalache.io.json.ScalaToJsonAdapter
import ujson._

/**
 * Adapter for converting Scala primitives to UJsonRep.
 */
object ScalaToUJsonAdapter extends ScalaToJsonAdapter[UJsonRepresentation] {
  import scala.language.implicitConversions

  implicit private def readVal(rep: UJsonRepresentation): Value = rep.value
  implicit private def lift(value: Value): UJsonRepresentation = UJsonRepresentation(value)

  override def mkObj(fields: (String, UJsonRepresentation)*): UJsonRepresentation = {
    // ujson defines a nullary and non-nullary Obj.apply method separately, so we have to improvise a bit
    if (fields.isEmpty) Obj()
    else {
      val (head, tail) = (fields.head, fields.tail.map { case (a, b) => (a, b.value) })
      Obj.apply(head, tail: _*)
    }
  }

  override def fromInt(int: Int): UJsonRepresentation = Value.JsonableInt(int)

  override def fromStr(str: String): UJsonRepresentation = Value.JsonableString(str)

  override def fromBool(bool: Boolean): UJsonRepresentation = Value.JsonableBoolean(bool)

  override def fromIterable(trv: Iterable[UJsonRepresentation]): UJsonRepresentation = Value.JsonableSeq(trv)
}

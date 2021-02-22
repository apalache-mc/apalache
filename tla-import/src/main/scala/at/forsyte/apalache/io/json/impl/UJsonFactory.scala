package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonFactory
import ujson._

/**
 * Factory for the UJsonRep variant of JsonRepresentation
 */
object UJsonFactory extends JsonFactory[UJsonRep] {
  implicit def readVal(rep: UJsonRep): Value = rep.value
  implicit def lift(value: Value): UJsonRep = UJsonRep(value)

  override def mkObj(fields: (String, UJsonRep)*): UJsonRep = {
    // ujson defines a nullary and non-nullary Obj.apply method separately, so we have to improvise a bit
    if (fields.isEmpty) Obj()
    else {
      val (head, tail) = (fields.head, fields.tail map { case (a, b) => (a, b.value) })
      Obj.apply(head, tail: _*)
    }
  }

  override def fromInt(int: Int): UJsonRep = Value.JsonableInt(int)

  override def fromStr(str: String): UJsonRep = Value.JsonableString(str)

  override def fromBool(bool: Boolean): UJsonRep = Value.JsonableBoolean(bool)

  override def fromTraversable(trv: Traversable[UJsonRep]): UJsonRep = Value.JsonableSeq(trv)
}

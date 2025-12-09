package at.forsyte.apalache.io.json.ujsonimpl

import at.forsyte.apalache.io.json.{JsonDeserializationError, ScalaFromJsonAdapter}

/**
 * Adapter for extracting Scala primitives from UJsonRep.
 */
object ScalaFromUJsonAdapter extends ScalaFromJsonAdapter[UJsonRepresentation] {
  override def asInt(json: UJsonRepresentation): Int =
    json.value.numOpt.map { _.toInt }.getOrElse {
      throw new JsonDeserializationError("Not an integer.")
    }

  override def asStr(json: UJsonRepresentation): String = json.value.strOpt.getOrElse {
    throw new JsonDeserializationError("Not a string.")
  }

  override def asBool(json: UJsonRepresentation): Boolean = json.value.boolOpt.getOrElse {
    throw new JsonDeserializationError("Not a Boolean.")
  }

  override def asSeq(json: UJsonRepresentation): Seq[UJsonRepresentation] =
    json.value.arrOpt
      .map { _.map(UJsonRepresentation) }
      .getOrElse {
        throw new JsonDeserializationError("Not an array.")
      }
      .toSeq
}

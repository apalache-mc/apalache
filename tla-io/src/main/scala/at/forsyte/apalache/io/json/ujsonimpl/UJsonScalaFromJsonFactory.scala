package at.forsyte.apalache.io.json.ujsonimpl

import at.forsyte.apalache.io.json.{JsonDeserializationError, ScalaFromJsonFactory}

/**
 * ScalaFactory for the UJsonRep variant of JsonRepresentation
 */
object UJsonScalaFromJsonFactory extends ScalaFromJsonFactory[UJsonRep] {
  override def asInt(json: UJsonRep): Int =
    json.value.numOpt.map { _.toInt }.getOrElse {
      throw new JsonDeserializationError("Not an integer.")
    }

  override def asStr(json: UJsonRep): String = json.value.strOpt.getOrElse {
    throw new JsonDeserializationError("Not a string.")
  }

  override def asBool(json: UJsonRep): Boolean = json.value.boolOpt.getOrElse {
    throw new JsonDeserializationError("Not a Boolean.")
  }

  override def asSeq(json: UJsonRep): Seq[UJsonRep] =
    json.value.arrOpt
      .map { _.map(UJsonRep) }
      .getOrElse {
        throw new JsonDeserializationError("Not an array.")
      }
      .toSeq
}

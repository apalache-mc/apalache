package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.json.{JsonDeserializationError, ScalaFromJsonAdapter}
import scala.jdk.CollectionConverters._

/**
 * Adapter for extracting Scala primitives from JacksonRep.
 */
object ScalaFromJacksonAdapter extends ScalaFromJsonAdapter[JacksonRep] {
  override def asInt(json: JacksonRep): Int = {
    if (json.value.isInt) {
      json.value.asInt()
    } else {
      throw new JsonDeserializationError("Not an integer.")
    }
  }

  override def asStr(json: JacksonRep): String = {
    if (json.value.isTextual) {
      json.value.asText()
    } else {
      throw new JsonDeserializationError("Not a string.")
    }
  }

  override def asBool(json: JacksonRep): Boolean = {
    if (json.value.isBoolean) {
      json.value.asBoolean()
    } else {
      throw new JsonDeserializationError("Not a Boolean.")
    }
  }

  override def asSeq(json: JacksonRep): Seq[JacksonRep] = {
    if (json.value.isArray) {
      json.value.elements().asScala.map(JacksonRep(_)).toSeq
    } else {
      throw new JsonDeserializationError("Not an array.")
    }
  }
}

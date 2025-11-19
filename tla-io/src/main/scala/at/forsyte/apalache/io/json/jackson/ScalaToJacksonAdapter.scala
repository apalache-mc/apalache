package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.json.ScalaToJsonAdapter
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.databind.node.{ArrayNode, ObjectNode}

/**
 * Adapter for converting Scala primitives to JacksonRep.
 */
object ScalaToJacksonAdapter extends ScalaToJsonAdapter[JacksonRepresentation] {
  private val mapper = new ObjectMapper()

  override def mkObj(fields: (String, JacksonRepresentation)*): JacksonRepresentation = {
    val objectNode: ObjectNode = mapper.createObjectNode()
    fields.foreach { case (key, rep) =>
      objectNode.set[JsonNode](key, rep.value)
      ()
    }
    JacksonRepresentation(objectNode)
  }

  override def fromInt(int: Int): JacksonRepresentation = {
    JacksonRepresentation(mapper.valueToTree(int))
  }

  override def fromStr(str: String): JacksonRepresentation = {
    JacksonRepresentation(mapper.valueToTree(str))
  }

  override def fromBool(bool: Boolean): JacksonRepresentation = {
    JacksonRepresentation(mapper.valueToTree(bool))
  }

  override def fromIterable(trv: Iterable[JacksonRepresentation]): JacksonRepresentation = {
    val arrayNode: ArrayNode = mapper.createArrayNode()
    trv.foreach(rep => arrayNode.add(rep.value))
    JacksonRepresentation(arrayNode)
  }
}

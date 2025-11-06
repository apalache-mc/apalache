package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.json.JsonFromScalaFactory
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.databind.node.{ArrayNode, ObjectNode}

/**
 * Factory for the JacksonRep variant of JsonRepresentation
 */
object JacksonFromScalaFactory extends JsonFromScalaFactory[JacksonRep] {
  private val mapper = new ObjectMapper()

  override def mkObj(fields: (String, JacksonRep)*): JacksonRep = {
    val objectNode: ObjectNode = mapper.createObjectNode()
    fields.foreach { case (key, rep) =>
      objectNode.set[JsonNode](key, rep.value)
    }
    JacksonRep(objectNode)
  }

  override def fromInt(int: Int): JacksonRep = {
    JacksonRep(mapper.valueToTree(int))
  }

  override def fromStr(str: String): JacksonRep = {
    JacksonRep(mapper.valueToTree(str))
  }

  override def fromBool(bool: Boolean): JacksonRep = {
    JacksonRep(mapper.valueToTree(bool))
  }

  override def fromIterable(trv: Iterable[JacksonRep]): JacksonRep = {
    val arrayNode: ArrayNode = mapper.createArrayNode()
    trv.foreach(rep => arrayNode.add(rep.value))
    JacksonRep(arrayNode)
  }
}


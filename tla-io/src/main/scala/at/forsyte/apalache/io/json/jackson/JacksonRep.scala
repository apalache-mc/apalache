package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.json.JsonRepresentation
import com.fasterxml.jackson.databind.JsonNode
import com.fasterxml.jackson.databind.ObjectMapper
import scala.jdk.CollectionConverters._

/**
 * A JsonRepresentation using Jackson's JsonNode.
 */
sealed case class JacksonRep(value: JsonNode) extends JsonRepresentation {
  type Value = JsonNode

  /** Pretty print the JSON representation */
  override def toString: String = {
    JacksonRep.mapper.writerWithDefaultPrettyPrinter().writeValueAsString(value)
  }

  /**
   * If `this` represents a JSON object defining a field `fieldName : val`, the method returns a Some(_), containing the
   * representation of `val`, otherwise (if `this` is not an object or if it does not define a `fieldName` field)
   * returns None.
   */
  override def getFieldOpt(fieldName: String): Option[this.type] = {
    if (value.isObject && value.has(fieldName)) {
      Some(JacksonRep(value.get(fieldName)).asInstanceOf[JacksonRep.this.type])
    } else {
      None
    }
  }

  /**
   * If `this` represents a JSON object, returns the set of all field names defined in the object. Otherwise, returns
   * None.
   */
  override def allFieldsOpt: Option[Set[String]] = {
    if (value.isObject) {
      Some(value.fieldNames().asScala.toSet)
    } else {
      None
    }
  }
}

object JacksonRep {
  private val mapper = new ObjectMapper()
}


package at.forsyte.apalache.io.json

/** Thrown, when importing from JSON fails, due to malformed input */
class JsonDeserializationError(msg: String) extends Exception(msg)

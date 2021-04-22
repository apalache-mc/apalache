package at.forsyte.apalache.io.json

/**
 * JSON serialization versions need not be tied to Apalache versions
 * (Apalache versions, obtained from at.forsyte.apalache.tla.tooling.Version
 * cannot be read here anyway, due to tooling -> import dependencies)
 */
object JsonVersion {
  val major = 1
  val minor = 0
  def current: String = s"$major.$minor"
}

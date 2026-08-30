package at.forsyte.apalache.tla.lir.storage

import com.google.inject.Singleton

import scala.collection.mutable

/**
 * Stores human-readable descriptions of generated variables.
 *
 * The store is scoped to a Guice injector, so descriptions are shared by the passes and output writers in one tool run
 * without leaking into other runs or JSON-RPC sessions.
 */
@Singleton
final class VariableDescriptionsStore {
  private val descriptions = mutable.HashMap.empty[String, String]

  def put(variableName: String, description: String): Unit =
    descriptions.update(variableName, description)

  def get(variableName: String): Option[String] =
    descriptions.get(variableName)

  def isEmpty: Boolean =
    descriptions.isEmpty

  def toMap: Map[String, String] =
    descriptions.toMap
}

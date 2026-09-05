package org.apalache_mc.tla.jir

import at.forsyte.apalache.tla.typecomp.{ScopeUnsafeBuilder, ScopedBuilder}
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import org.scalatest.funsuite.AnyFunSuite

import java.lang.reflect.Method

/**
 * Guards the Java facade against silent API drift in the underlying Scala builders.
 *
 * The test reads `builder-operation-inventory.json` from the test classpath with Jackson. The JSON object has
 * `ScopedBuilder` and `ScopeUnsafeBuilder` members for the corresponding Scala builder classes. Each member contains a
 * `methods` array of objects with `scalaSig` and `javaMethod` fields, plus an `ignored` array of objects with
 * `scalaMethod` and `reason` fields. Exact JVM descriptors distinguish overloads and detect parameter or return-type
 * changes; mapped names also record intentional Java renames such as `int -> integer` and `const -> constant`.
 *
 * The inventory is deliberately checked in rather than generated during the test. A generated inventory would always
 * mirror the current builders and could not reveal that a method was added, removed, or changed. Comparing reflection
 * results with this fixed snapshot makes such a change fail the test until maintainers either expose the operation in
 * the facade, update its mapping, or add a justified ignored entry for an unsupported internal or deprecated operation.
 *
 * This is a maintenance test only: the resource is not included in the published facade artifact. It verifies that
 * every inventoried source operation has a facade method with the mapped name and that the facade exposes no
 * unaccounted public method names. The checked facade's `build` methods are the sole facade-only allowance because they
 * materialize opaque builder state rather than wrapping Scala builder operations. The test does not prove behavioral
 * equivalence or an exact facade descriptor. The behavioral tests, public-signature audit, and external Java consumer
 * cover those concerns separately.
 */
class TestOperationInventory extends AnyFunSuite {
  test("every stable Scala builder and facade method has an explicit inventory decision") {
    check(
        "ScopedBuilder",
        classOf[ScopedBuilder],
        classOf[TlaCheckedBuilder],
        facadeOnlyMethods = Set("build"),
    )
    check("ScopeUnsafeBuilder", classOf[ScopeUnsafeBuilder], classOf[TlaTypedScopeUncheckedBuilder])
  }

  private def check(
      section: String,
      scalaBuilder: Class[_],
      javaBuilder: Class[_],
      facadeOnlyMethods: Set[String] = Set.empty): Unit = {
    val (expected, ignored) = expectedSection(section)
    assert(sourceInventory(scalaBuilder, ignored) == expected.keySet)
    val expectedFacadeMethods = expected.values.toSet ++ facadeOnlyMethods
    val actualFacadeMethods = javaBuilder.getMethods.iterator
      .filterNot(_.getDeclaringClass == classOf[Object])
      .map(_.getName)
      .toSet
    val missing = expectedFacadeMethods -- actualFacadeMethods
    val additional = actualFacadeMethods -- expectedFacadeMethods
    assert(missing.isEmpty, s"$section facade is missing public methods: ${missing.toSeq.sorted.mkString(", ")}")
    assert(
        additional.isEmpty,
        s"$section facade has unaccounted public methods: ${additional.toSeq.sorted.mkString(", ")}",
    )
  }

  private def expectedSection(name: String): (Map[String, String], Set[String]) = {
    val section = requiredObject(inventory, name)
    val methodEntries = elements(requiredArray(section, "methods")).map { method =>
      requiredText(method, "scalaSig") -> requiredText(method, "javaMethod")
    }
    assert(methodEntries.map(_._1).distinct.size == methodEntries.size, s"Duplicate $name scalaSig")

    val ignoredEntries = elements(requiredArray(section, "ignored")).map { method =>
      requiredText(method, "scalaMethod") -> requiredText(method, "reason")
    }
    assert(ignoredEntries.map(_._1).distinct.size == ignoredEntries.size, s"Duplicate $name ignored method")
    assert(ignoredEntries.forall(_._2.nonEmpty), s"Every $name ignored method must have a reason")
    methodEntries.toMap -> ignoredEntries.map(_._1).toSet
  }

  private def sourceInventory(builderClass: Class[_], ignored: Set[String]): Set[String] =
    builderClass.getMethods.iterator
      .filter(method => method.getDeclaringClass == builderClass)
      .filterNot(method => method.getName.contains("$") || ignored.contains(method.getName))
      .map(descriptor)
      .toSet

  private def descriptor(method: Method): String =
    method.getName + method.getParameterTypes.map(typeDescriptor).mkString("(", "", ")") + typeDescriptor(
        method.getReturnType
    )

  private def typeDescriptor(clazz: Class[_]): String = {
    if (clazz.isArray) "[" + typeDescriptor(clazz.getComponentType)
    else if (!clazz.isPrimitive) "L" + clazz.getName.replace('.', '/') + ";"
    else if (clazz == java.lang.Boolean.TYPE) "Z"
    else if (clazz == java.lang.Byte.TYPE) "B"
    else if (clazz == java.lang.Character.TYPE) "C"
    else if (clazz == java.lang.Short.TYPE) "S"
    else if (clazz == java.lang.Integer.TYPE) "I"
    else if (clazz == java.lang.Long.TYPE) "J"
    else if (clazz == java.lang.Float.TYPE) "F"
    else if (clazz == java.lang.Double.TYPE) "D"
    else if (clazz == java.lang.Void.TYPE) "V"
    else throw new IllegalArgumentException(s"Unknown primitive $clazz")
  }

  private def requiredObject(parent: JsonNode, name: String): JsonNode = {
    val child = parent.get(name)
    assert(child != null && child.isObject, s"Expected JSON object at $name")
    child
  }

  private def requiredArray(parent: JsonNode, name: String): JsonNode = {
    val child = parent.get(name)
    assert(child != null && child.isArray, s"Expected JSON array at $name")
    child
  }

  private def requiredText(parent: JsonNode, name: String): String = {
    val child = parent.get(name)
    assert(child != null && child.isTextual, s"Expected JSON string at $name")
    child.asText()
  }

  private def elements(array: JsonNode): IndexedSeq[JsonNode] =
    (0 until array.size()).map(array.get)

  private lazy val inventory: JsonNode = {
    val stream = Option(getClass.getResourceAsStream("/builder-operation-inventory.json"))
      .getOrElse(fail("Missing builder-operation-inventory.json"))
    try new ObjectMapper().readTree(stream)
    finally stream.close()
  }
}

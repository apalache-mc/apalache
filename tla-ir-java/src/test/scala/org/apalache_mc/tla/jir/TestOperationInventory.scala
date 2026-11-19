package org.apalache_mc.tla.jir

import at.forsyte.apalache.tla.typecomp.{ScopeUnsafeBuilder, ScopedBuilder}
import org.scalatest.funsuite.AnyFunSuite

/** Compares the operations exposed by the Scala builders and their Java facades. */
class TestOperationInventory extends AnyFunSuite {
  test("every supported Scala builder operation has a Java facade operation") {
    check(classOf[ScopedBuilder], classOf[TlaCheckedBuilder], facadeOnly = Set("build"))
    check(classOf[ScopeUnsafeBuilder], classOf[TlaTypedScopeUncheckedBuilder])
  }

  private def check(
      scalaBuilder: Class[_],
      javaBuilder: Class[_],
      facadeOnly: Set[String] = Set.empty): Unit = {
    val scalaOperations = scalaBuilder.getMethods.iterator
      .filter(_.getDeclaringClass == scalaBuilder)
      .map(_.getName)
      .filterNot(name => name.contains("$") || excludedOperations.contains(name))
      .map(name => renamedOperations.getOrElse(name, name))
      .toSet
    val facadeOperations = javaBuilder.getMethods.iterator
      .filterNot(_.getDeclaringClass == classOf[Object])
      .map(_.getName)
      .toSet -- facadeOnly

    assert(
        scalaOperations == facadeOperations,
        s"${scalaBuilder.getSimpleName}/${javaBuilder.getSimpleName} operation mismatch: " +
          s"missing=${(scalaOperations -- facadeOperations).toSeq.sorted.mkString(",")}; " +
          s"additional=${(facadeOperations -- scalaOperations).toSeq.sorted.mkString(",")}",
    )
  }

  // The Java facade uses descriptive Java names where the Scala DSL uses symbols,
  // abbreviations, overloaded names, or Java keywords.
  private val renamedOperations = Map(
      "AA" -> "temporalForAll",
      "EE" -> "temporalExists",
      "SF" -> "strongFair",
      "WF" -> "weakFair",
      "app" -> "funApply",
      "appOp" -> "operApply",
      "box" -> "always",
      "cap" -> "intersect",
      "comp" -> "actionThen",
      "const" -> "constant",
      "cup" -> "union",
      "diamond" -> "eventually",
      "dom" -> "domain",
      "dotdot" -> "interval",
      "impl" -> "implies",
      "int" -> "integer",
      "nostutt" -> "noStutter",
      "notin" -> "notIn",
      "powSet" -> "powerSet",
      "recSet" -> "recordSet",
      "rowRec" -> "record",
      "setminus" -> "difference",
      "stutt" -> "stutter",
      "subseq" -> "subSeq",
      "subseteq" -> "subsetEq",
      "union" -> "unionAll",
  )

  // These are configuration accessors, legacy/deprecated forms superseded by the
  // structured facade, or model-checker implementation operations rather than IR builders.
  private val excludedOperations = Set(
      "buildBySignatureLookup",
      "caseOtherMixed",
      "caseSplitMixed",
      "cmpFactory",
      "exceptDeep",
      "exceptGeneral",
      "funDefMixed",
      "mapMixed",
      "rec",
      "recMixed",
      "recSetMixed",
      "rowRecMixed",
      "selectInFun",
      "selectInSet",
      "smtMap",
      "storeInSet",
      "storeNotInFun",
      "storeNotInSet",
      "strict",
      "unconstrainArray",
  )
}

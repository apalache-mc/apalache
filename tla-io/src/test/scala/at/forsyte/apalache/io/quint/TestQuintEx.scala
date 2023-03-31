package at.forsyte.apalache.io.quint

import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.lir.Typed
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import QuintType._
import QuintEx._

// You can run all these tests in watch mode in the
// sbt console with
//
//      sbt:apalache> ~tla_io/testOnly *TestQuint*

/**
 * Tests the conversion of quint expressions and declarations into TLA expressions
 */
@RunWith(classOf[JUnitRunner])
class TestQuintEx extends AnyFunSuite {

  // Quint expressions used in the unit tests
  object Q {

    // expression IDs must be unique, and any constructed
    // expression should use this thunk to produce a
    // unique ID (uid)
    private var nextId = 1
    private def uid: Int = {
      val x = nextId
      nextId += 1
      x
    }

    // Operator application
    def app(name: String, args: QuintEx*): QuintApp = QuintApp(uid, name, args)

    // Scalar values
    val tt = QuintBool(uid, true)
    val _0 = QuintInt(uid, 0)
    val _1 = QuintInt(uid, 1)
    val _2 = QuintInt(uid, 2)
    val _3 = QuintInt(uid, 3)
    val _42 = QuintInt(uid, 42)
    val s = QuintStr(uid, "s")

    // Names and parameters
    val name = QuintName(uid, "n")
    val nParam = QuintLambdaParameter(uid, "n")
    val acc = QuintName(uid, "acc")
    val accParam = QuintLambdaParameter(uid, "acc")
    val xParam = QuintLambdaParameter(uid, "x")
    val namedIntToBoolOp = QuintName(uid, "intToBoolOp")

    // Definitions and compound data types
    val fooDef = QuintDef.QuintOpDef(uid, "foo", "val", tt)
    val letFooBeTrueIn42 = QuintLet(uid, fooDef, _42)
    val lambda = QuintLambda(uid, List(xParam), "def", s)
    // Applications can only be by name (lambdas are not first class)
    val barDef = QuintDef.QuintOpDef(uid, "bar", "def", lambda)
    val appBar = QuintApp(uid, "bar", List(_42))
    val letBarBeLambdaInAppBar = QuintLet(uid, barDef, appBar)
    val nIsGreaterThan0 = app("igt", name, _0)
    val nDefindedAs42 = QuintDef.QuintOpDef(uid, "n", "val", _42)
    val letNbe42inNisGreaterThan0 = QuintLet(uid, nDefindedAs42, nIsGreaterThan0)
    // A predicate on ints
    val intIsGreaterThanZero = QuintLambda(uid, List(nParam), "def", nIsGreaterThan0)
    val int2ToBool = QuintLambda(uid, List(nParam, accParam), "def", tt)
    val intSet = app("Set", _1, _2, _3)
    val intPair = app("Tup", _1, _2)
    val intList = app("List", _1, _2, _3)
    val intPairSet = app("Set", intPair, intPair)
    val emptyIntList = app("List")
    val emptyIntSet = app("Set")
    val setOfIntSets = app("Set", intSet, intSet, intSet)
    val intTup1 = app("Tup", _0, _1)
    val intTup2 = app("Tup", _3, _42)
    val intMap = app("Map", intTup1, intTup2) // Map(0 -> 1, 3 -> 42)
    // For use in folds
    val addNameAndAcc = app("iadd", name, acc)
    val accumulatingOpp = QuintLambda(uid, List(accParam, nParam), "def", addNameAndAcc)
    val chooseSomeFromIntSet = app("chooseSome", intSet)
    val oneOfSet = app("oneOf", intSet)
    val nondetBinding = QuintLet(uid, QuintDef.QuintOpDef(uid, "n", "nondet", oneOfSet), nIsGreaterThan0)
    // Requires ID registered with type
    val selectGreaterThanZero = app("select", intList, intIsGreaterThanZero)
    val addOne = app("iadd", name, _1)
    val addOneOp = QuintLambda(uid, List(nParam), "def", addOne)
    val setByExpression = app("setBy", intMap, _1, addOneOp)
    val selectIntIsGreaterThanZero = app("select", intList, intIsGreaterThanZero)
    val selectNamedIntToBoolOp = app("select", intList, namedIntToBoolOp)
  }

  // The Quint conversion class requires a QuintOutput object which,
  // to enable expression conversion, requires a correctly constructed
  // map of expression IDs to their inferred and checked types.
  val typeMapping: Map[QuintEx, QuintType] = Map(
      Q.tt -> QuintBoolT(),
      Q._0 -> QuintIntT(),
      Q._1 -> QuintIntT(),
      Q._2 -> QuintIntT(),
      Q._3 -> QuintIntT(),
      Q._42 -> QuintIntT(),
      Q.s -> QuintStrT(),
      Q.name -> QuintIntT(),
      Q.acc -> QuintIntT(),
      Q.namedIntToBoolOp -> QuintOperT(Seq(QuintIntT()), QuintBoolT()),
      Q.letFooBeTrueIn42 -> QuintBoolT(),
      Q.lambda -> QuintOperT(List(QuintIntT()), QuintStrT()),
      Q.appBar -> QuintStrT(),
      Q.letBarBeLambdaInAppBar -> QuintStrT(),
      Q.nIsGreaterThan0 -> QuintBoolT(),
      Q.letNbe42inNisGreaterThan0 -> QuintBoolT(),
      Q.int2ToBool -> QuintOperT(List(QuintIntT(), QuintIntT()), QuintBoolT()),
      Q.intIsGreaterThanZero -> QuintOperT(List(QuintIntT()), QuintBoolT()),
      Q.intSet -> QuintSetT(QuintIntT()),
      Q.intPair -> QuintTupleT.ofTypes(QuintIntT(), QuintIntT()),
      Q.intList -> QuintSeqT(QuintIntT()),
      Q.intPairSet -> QuintSetT(QuintTupleT.ofTypes(QuintIntT(), QuintIntT())),
      Q.emptyIntSet -> QuintSetT(QuintIntT()),
      Q.setOfIntSets -> QuintSetT(QuintSetT(QuintIntT())),
      Q.addNameAndAcc -> QuintIntT(),
      Q.accumulatingOpp -> QuintOperT(List(QuintIntT(), QuintIntT()), QuintIntT()),
      Q.chooseSomeFromIntSet -> QuintIntT(),
      Q.intMap -> QuintFunT(QuintIntT(), QuintIntT()),
      Q.addOne -> QuintIntT(),
      Q.addOneOp -> QuintOperT(List(QuintIntT()), QuintIntT()),
      Q.selectGreaterThanZero -> QuintSeqT(QuintIntT()),
      Q.setByExpression -> QuintFunT(QuintIntT(), QuintIntT()),
      Q.oneOfSet -> QuintIntT(),
      Q.nondetBinding -> QuintIntT(),
      Q.emptyIntList -> QuintSeqT(QuintIntT()),
      Q.selectNamedIntToBoolOp -> QuintSeqT(QuintIntT()),
      Q.selectIntIsGreaterThanZero -> QuintSeqT(QuintIntT()),
  )

  // We construct a converter supplied with the needed type map
  def quint = new Quint(QuintOutput(
          "typechecking",
          List(QuintModule(0, "MockedModule", List())),
          typeMapping.map { case (ex, typ) =>
            // Wrap each type in the TypeScheme required by the Quint IR
            ex.id -> QuintTypeScheme(typ)
          },
      ))

  // Convert a quint expression to TLA and render as a string
  def convert(qex: QuintEx): String = {
    quint.exToTla(qex).get.toString()
  }

  test("can convert boolean") {
    assert(convert(Q.tt) == "TRUE")
  }

  test("can convert int") {
    assert(convert(Q._42) == "42")
  }

  test("can convert str") {
    assert(convert(Q.s) == "\"s\"")
  }

  test("can convert name") {
    assert(convert(Q.name) == "n")
  }

  test("can convert let expression") {
    assert(convert(Q.letFooBeTrueIn42) == "LET foo ≜ TRUE IN 42")
  }

  test("can convert lambda") {
    assert(convert(Q.lambda) == """LET __QUINT_LAMBDA0(x) ≜ "s" IN __QUINT_LAMBDA0""")
  }

  test("can convert multi argument lambda") {
    assert(convert(Q.accumulatingOpp) == """LET __QUINT_LAMBDA0(acc, n) ≜ n + acc IN __QUINT_LAMBDA0""")
  }

  test("can convert operator application") {
    assert(convert(Q.letBarBeLambdaInAppBar) == """LET bar(x) ≜ "s" IN bar(42)""")
  }

  // Booleans
  test("can convert builtin eq operator application") {
    assert(convert(Q.app("eq", Q.tt, Q.tt)) == "TRUE = TRUE")
  }

  test("can convert builtin neq operator application") {
    assert(convert(Q.app("neq", Q.tt, Q.tt)) == "TRUE ≠ TRUE")
  }

  test("can convert builtin iff operator application") {
    assert(convert(Q.app("iff", Q.tt, Q.tt)) == "TRUE ⇔ TRUE")
  }

  test("can convert builtin implies operator application") {
    assert(convert(Q.app("implies", Q.tt, Q.tt)) == "TRUE ⇒ TRUE")
  }

  test("can convert builtin not operator application") {
    assert(convert(Q.app("not", Q.tt)) == "¬TRUE")
  }

  test("can convert builtin and operator application") {
    assert(convert(Q.app("and", Q.tt, Q.tt)) == "TRUE ∧ TRUE")
  }

  test("can convert builtin or operator application") {
    assert(convert(Q.app("or", Q.tt, Q.tt)) == "TRUE ∨ TRUE")
  }

  // Integers
  test("can convert builtin iadd operator application") {
    assert(convert(Q.app("iadd", Q._42, Q._42)) == "42 + 42")
  }

  test("can convert builtin isub operator application") {
    assert(convert(Q.app("isub", Q._42, Q._42)) == "42 - 42")
  }

  test("can convert builtin imul operator application") {
    assert(convert(Q.app("imul", Q._42, Q._42)) == "42 * 42")
  }

  test("can convert builtin idiv operator application") {
    assert(convert(Q.app("idiv", Q._42, Q._42)) == "42 // 42")
  }

  test("can convert builtin imod operator application") {
    assert(convert(Q.app("imod", Q._42, Q._42)) == "42 % 42")
  }

  test("can convert builtin ipow operator application") {
    assert(convert(Q.app("ipow", Q._42, Q._42)) == "42 ^ 42")
  }

  test("can convert builtin ilt operator application") {
    assert(convert(Q.app("ilt", Q._42, Q._42)) == "42 < 42")
  }

  test("can convert builtin igt operator application") {
    assert(convert(Q.app("igt", Q._42, Q._42)) == "42 > 42")
  }

  test("can convert builtin ilte operator application") {
    assert(convert(Q.app("ilte", Q._42, Q._42)) == "42 ≤ 42")
  }

  test("can convert builtin igte operator application") {
    assert(convert(Q.app("igte", Q._42, Q._42)) == "42 ≥ 42")
  }

  test("can convert builtin iuminus operator application") {
    assert(convert(Q.app("iuminus", Q._42)) == "-42")
  }

  test("can convert builtin Set operator application") {
    assert(convert(Q.app("Set", Q.s, Q.s, Q.s)) == """{"s", "s", "s"}""")
  }

  test("can convert builtin Set operator application for empty sets") {
    val tlaEx = quint.exToTla(Q.emptyIntSet).get
    // Ensure the constructed empty set has the required type
    assert(tlaEx.typeTag match {
      case Typed(SetT1(IntT1)) => true
      case _                   => false
    })
    assert(tlaEx.toString() == """{}""")
  }

  test("can convert builtin exists operator application") {
    assert(convert(Q.app("exists", Q.intSet, Q.intIsGreaterThanZero)) == "∃n ∈ {1, 2, 3}: (n > 0)")
  }

  test("can convert builtin exists operator application using tuple-bound names") {
    assert(convert(Q.app("exists", Q.intPairSet, Q.int2ToBool)) == "∃(<<n, acc>>) ∈ {<<1, 2>>, <<1, 2>>}: TRUE")
  }

  test("can convert builtin forall operator application") {
    assert(convert(Q.app("forall", Q.intSet, Q.intIsGreaterThanZero)) == "∀n ∈ {1, 2, 3}: (n > 0)")
  }

  test("can convert builtin forall operator application using tuple-bound names") {
    assert(convert(Q.app("forall", Q.intPairSet, Q.int2ToBool)) == "∀(<<n, acc>>) ∈ {<<1, 2>>, <<1, 2>>}: TRUE")
  }

  test("converting binary binding operator with missing lambda fails") {
    val exn = intercept[QuintIRParseError] {
      convert(Q.app("forall", Q.intSet, Q.intSet))
    }
    assert(exn.getMessage.contains(
            "Input was not a valid representation of the QuintIR: Operator forall is a binding operator requiring a lambda as it's second argument"))
  }

  test("converting binary binding operator with invalid arity fails") {
    val exn = intercept[QuintIRParseError] {
      convert(Q.app("forall", Q.intSet))
    }
    assert(exn.getMessage.contains(
            "Input was not a valid representation of the QuintIR: too many arguments passed to binary operator forall"))
  }

  test("can convert builtin in operator application") {
    assert(convert(Q.app("in", Q._1, Q.intSet)) == "1 ∈ {1, 2, 3}")
  }

  test("can convert builtin contains operator application") {
    assert(convert(Q.app("contains", Q.intSet, Q._1)) == "1 ∈ {1, 2, 3}")
  }

  test("can convert builtin notin operator application") {
    assert(convert(Q.app("notin", Q._1, Q.intSet)) == "1 ∉ {1, 2, 3}")
  }

  test("can convert builtin union operator application") {
    assert(convert(Q.app("union", Q.intSet, Q.intSet)) == "{1, 2, 3} ∪ {1, 2, 3}")
  }

  test("can convert builtin intersect operator application") {
    assert(convert(Q.app("intersect", Q.intSet, Q.intSet)) == "{1, 2, 3} ∩ {1, 2, 3}")
  }

  test("can convert builtin exclude operator application") {
    assert(convert(Q.app("exclude", Q.intSet, Q.intSet)) == "{1, 2, 3} ∖ {1, 2, 3}")
  }

  test("can convert builtin subseteq operator application") {
    assert(convert(Q.app("subseteq", Q.intSet, Q.intSet)) == "{1, 2, 3} ⊆ {1, 2, 3}")
  }

  test("can convert builtin filter operator application") {
    assert(convert(Q.app("filter", Q.intSet, Q.intIsGreaterThanZero)) == "{n ∈ {1, 2, 3}: (n > 0)}")
  }

  test("can convert builtin map operator application") {
    assert(convert(Q.app("map", Q.intSet, Q.intIsGreaterThanZero)) == "{n > 0 : n ∈ {1, 2, 3}}")
  }

  test("can convert builtin fold operator application") {
    val expected = "Apalache!ApaFoldSet(LET __QUINT_LAMBDA0(acc, n) ≜ n + acc IN __QUINT_LAMBDA0, 1, {1, 2, 3})"
    assert(convert(Q.app("fold", Q.intSet, Q._1, Q.accumulatingOpp)) == expected)
  }

  test("can convert builtin powerset operator application") {
    assert(convert(Q.app("powerset", Q.intSet)) == "SUBSET {1, 2, 3}")
  }

  test("can convert builtin flatten operator application") {
    assert(convert(Q.app("flatten", Q.setOfIntSets)) == "UNION {{1, 2, 3}, {1, 2, 3}, {1, 2, 3}}")
  }

  test("can convert builtin allLists operator application") {
    assert(convert(Q.app("allLists", Q.intSet)) == "Seq({1, 2, 3})")
  }

  test("can convert builtin chooseSome operator application") {
    assert(convert(Q.chooseSomeFromIntSet) == "CHOOSE __quint_var0 ∈ {1, 2, 3} : TRUE")
  }

  test("can convert builtin isFinite operator application") {
    assert(convert(Q.app("isFinite", Q.intSet)) == "IsFiniteSet({1, 2, 3})")
  }

  test("can convert builtin size operator application") {
    assert(convert(Q.app("size", Q.intSet)) == "Cardinality({1, 2, 3})")
  }

  test("can convert builtin to operator application") {
    assert(convert(Q.app("to", Q._1, Q._42)) == "1 .. 42")
  }

  test("can convert builtin List operator application") {
    assert(convert(Q.app("List", Q._1, Q._2, Q._3)) == "<<1, 2, 3>>")
  }

  test("can convert builtin List operator application for empty list") {
    assert(convert(Q.emptyIntList) == "<<>>")
  }

  test("can convert builtin append operator application") {
    assert(convert(Q.app("append", Q.intList, Q._42)) == "Append(<<1, 2, 3>>, 42)")
  }

  test("can convert builtin concat operator application") {
    assert(convert(Q.app("concat", Q.intList, Q.intList)) == "(<<1, 2, 3>>) ∘ (<<1, 2, 3>>)")
  }

  test("can convert builtin head operator application") {
    assert(convert(Q.app("head", Q.intList)) == "Head(<<1, 2, 3>>)")
  }

  test("can convert builtin tail operator application") {
    assert(convert(Q.app("tail", Q.intList)) == "Tail(<<1, 2, 3>>)")
  }

  test("can convert builtin length operator application") {
    assert(convert(Q.app("length", Q.intList)) == "Len(<<1, 2, 3>>)")
  }

  test("can convert builtin indices operator application") {
    val expected =
      "LET __quint_var0 ≜ DOMAIN (<<1, 2, 3>>) IN IF (__quint_var0() = {}) THEN {} ELSE ((__quint_var0() ∪ {0}) ∖ {Len(<<1, 2, 3>>)})"
    assert(convert(Q.app("indices", Q.intList)) == expected)
  }

  test("can convert builtin foldl operator application") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA0(acc, n) ≜ n + acc IN __QUINT_LAMBDA0, 0, <<1, 2, 3>>)"
    assert(convert(Q.app("foldl", Q.intList, Q._0, Q.accumulatingOpp)) == expected)
  }

  test("can convert builtin nth operator application") {
    assert(convert(Q.app("nth", Q.intList, Q._1)) == "(<<1, 2, 3>>)[1 + 1]")
  }

  test("can convert builtin nth operator application to variable index") {
    assert(convert(Q.app("nth", Q.intList, Q.name)) == "(<<1, 2, 3>>)[n + 1]")
  }

  test("can convert builtin replaceAt operator application") {
    assert(convert(Q.app("replaceAt", Q.intList, Q._1, Q._42)) == "[<<1, 2, 3>> EXCEPT ![(1 + 1)] = 42]")
  }

  test("can convert builtin slice operator application") {
    assert(convert(Q.app("slice", Q.intList, Q._0, Q._1)) == "Sequences!SubSeq(<<1, 2, 3>>, 0 + 1, 1 + 1)")
  }

  test("can convert builtin select operator application") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA0(__quint_var0, n) ≜ IF (n > 0) THEN (Append(__quint_var0, n)) ELSE __quint_var0 IN __QUINT_LAMBDA0, <<>>, <<1, 2, 3>>)"
    assert(convert(Q.selectIntIsGreatexThanZero) == expected)
  }

  test("can convert builtin select operator application with named test operator") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA0(__quint_var1, __quint_var0) ≜ IF (intToBoolOp(__quint_var0)) THEN (Append(__quint_var1, __quint_var0)) ELSE __quint_var1 IN __QUINT_LAMBDA0, <<>>, <<1, 2, 3>>)"
    assert(convert(Q.selectNamedIntToBoolOp) == expected)
  }

  test("can convert builtin range operator application") {
    assert(convert(Q.app("range", Q._3,
            Q._42)) == "Apalache!MkSeq(42 - 3, LET __QUINT_LAMBDA0(__quint_var0) ≜ (3 + __quint_var0) - 1 IN __QUINT_LAMBDA0)")
  }

  test("can convert builtin Tup operator application") {
    assert(convert(Q.app("Tup", Q._0, Q._1)) == "<<0, 1>>")
  }

  test("can convert builtin Tup operator application to heterogeneous elemens") {
    assert(convert(Q.app("Tup", Q._0, Q.s)) == "<<0, \"s\">>")
  }

  test("can convert builtin item operator application") {
    assert(convert(Q.app("item", Q.intPair, Q._1)) == "(<<1, 2>>)[1]")
  }

  test("can convert builtin tuples operator application") {
    assert(convert(Q.app("tuples", Q.intSet, Q.intSet, Q.intSet)) == "{1, 2, 3} × {1, 2, 3} × {1, 2, 3}")
  }

  test("can convert builtin assert operator") {
    assert(convert(Q.app("assert", Q.nIsGreaterThan0)) == "n > 0")
  }

  test("can convert builtin Map operator") {
    assert(convert(Q.app("Map", Q.intTup1, Q.intTup2)) == "Apalache!SetAsFun({<<0, 1>>, <<3, 42>>})")
  }

  test("can convert builtin get operator") {
    assert(convert(Q.app("get", Q.intMap, Q._0)) == "Apalache!SetAsFun({<<0, 1>>, <<3, 42>>})[0]")
  }

  test("can convert builtin keys operator") {
    assert(convert(Q.app("keys", Q.intMap)) == "DOMAIN Apalache!SetAsFun({<<0, 1>>, <<3, 42>>})")
  }

  test("can convert builtin setToMap operator") {
    assert(convert(Q.app("setToMap", Q.intPairSet)) == "Apalache!SetAsFun({<<1, 2>>, <<1, 2>>})")
  }

  test("can convert builtin setOfMaps operator") {
    assert(convert(Q.app("setOfMaps", Q.intSet, Q.intSet)) == "[{1, 2, 3} → {1, 2, 3}]")
  }

  test("can convert builtin set operator") {
    assert(
        convert(Q.app("set", Q.intMap, Q._3, Q._2))
          ==
            "[Apalache!SetAsFun({<<0, 1>>, <<3, 42>>}) EXCEPT ![3] = 2]"
    )
  }

  test("can convert builtin mapBy operator") {
    assert(convert(Q.app("mapBy", Q.intSet, Q.addOneOp)) == "[n ∈ {1, 2, 3} ↦ n + 1]")
  }

  test("can convert builtin setBy operator") {
    val expected = """
        |LET __quint_var0 ≜ Apalache!SetAsFun({<<0, 1>>, <<3, 42>>}) IN
        |[__quint_var0() EXCEPT ![1] = (LET __QUINT_LAMBDA0(n) ≜ n + 1 IN __QUINT_LAMBDA0(__quint_var0()[1]))]
        """.stripMargin.linesIterator.mkString(" ").trim
    assert(convert(Q.setByExpression) == expected)
  }

  test("can convert builtin put operator application") {
    val expected = """
        |LET __quint_var0 ≜ Apalache!SetAsFun({<<0, 1>>, <<3, 42>>}) IN
        |LET __quint_var1 ≜ DOMAIN __quint_var0() IN
        |[__quint_var2 ∈ ({3} ∪ __quint_var1()) ↦ IF (__quint_var2 = 3) THEN 42 ELSE __quint_var0()[__quint_var2]]
        """.stripMargin.linesIterator.mkString(" ").trim
    assert(convert(Q.app("put", Q.intMap, Q._3, Q._42)) == expected)
  }

  test("can convert nondet bindings") {
    assert(convert(Q.nondetBinding) == "∃n ∈ {1, 2, 3}: (n > 0)")
  }

  test("can convert let binding with reference to name in scope") {
    assert(convert(Q.letNbe42inNisGreaterThan0) == "LET n ≜ 42 IN n() > 0")
  }
}

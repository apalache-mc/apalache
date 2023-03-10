package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import QuintType._
import QuintEx._
import at.forsyte.apalache.tla.lir.Typed
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.lir.IntT1

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

    // Definitions and compound data types
    val fooDef = QuintDef.QuintOpDef(uid, "foo", "val", tt)
    val letFooBeTrueIn42 = QuintLet(uid, fooDef, _42)
    val lambda = QuintLambda(uid, List(xParam), "def", s)
    // Applications can only be by name (lambdas are not first class)
    val barDef = QuintDef.QuintOpDef(uid, "bar", "def", lambda)
    val appBar = QuintApp(uid, "bar", List(_42))
    val letBarBeLambdaInAppBar = QuintLet(uid, barDef, appBar)
    val nIsGreaterThanZero = app("igt", name, _0)
    // A predicate on ints
    val intIsGreaterThanZero = QuintLambda(uid, List(nParam), "def", nIsGreaterThanZero)
    val int2ToBool = QuintLambda(uid, List(nParam, accParam), "def", tt)
    val intSet = app("Set", _1, _2, _3)
    val intPair = app("Tup", _1, _2)
    val intList = app("List", _1, _2, _3)
    val intPairSet = app("Set", intPair, intPair)
    val emptyIntSet = app("Set")
    val setOfIntSets = app("Set", intSet, intSet, intSet)
    // For use in folds
    val addNameAndAcc = app("isum", name, acc)
    val accumulatingOpp = QuintLambda(uid, List(accParam, nParam), "def", addNameAndAcc)
    val chooseSomeFromIntSet = app("chooseSome", intSet)
    // Requires ID registered with type
    val selectGreaterThanZero = app("select", intList, intIsGreaterThanZero)
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
      Q.letFooBeTrueIn42 -> QuintBoolT(),
      Q.lambda -> QuintOperT(List(QuintIntT()), QuintStrT()),
      Q.appBar -> QuintStrT(),
      Q.letBarBeLambdaInAppBar -> QuintStrT(),
      Q.nIsGreaterThanZero -> QuintBoolT(),
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
      Q.selectGreaterThanZero -> QuintSeqT(QuintIntT()),
  )

  // We construct a converter supplied with the needed type map
  val quint = new Quint(QuintOutput(
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
    assert(convert(Q.accumulatingOpp) == """LET __QUINT_LAMBDA1(acc, n) ≜ isum(n, acc) IN __QUINT_LAMBDA1""")
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
    val expected = "Apalache!ApaFoldSet(LET __QUINT_LAMBDA2(acc, n) ≜ isum(n, acc) IN __QUINT_LAMBDA2, 1, {1, 2, 3})"
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
    assert(convert(Q.app("indices", Q.intList)) == "DOMAIN (<<1, 2, 3>>)")
  }

  test("can convert builtin foldl operator application") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA3(acc, n) ≜ isum(n, acc) IN __QUINT_LAMBDA3, 0, <<1, 2, 3>>)"
    assert(convert(Q.app("foldl", Q.intList, Q._0, Q.accumulatingOpp)) == expected)
  }

  test("can convert builtin nth operator application") {
    assert(convert(Q.app("nth", Q.intList, Q._1)) == "(<<1, 2, 3>>)[2]")
  }

  test("can convert builtin replaceAt operator application") {
    assert(convert(Q.app("replaceAt", Q.intList, Q._1, Q._42)) == "[<<1, 2, 3>> EXCEPT ![2] = 42]")
  }

  test("can convert builtin slice operator application") {
    assert(convert(Q.app("slice", Q.intList, Q._0, Q._1)) == "Sequences!SubSeq(<<1, 2, 3>>, 1, 2)")
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
}

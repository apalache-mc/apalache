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

    // The Quint conversion class requires a QuintOutput object which,
    // to enable expression conversion, requires a correctly constructed
    // map of expression IDs to their inferred and checked types.
    // This mutable map is used to register those types to record a type
    // map for the expressions entered in the Q object
    private val typeMap = collection.mutable.Map[Int, QuintType]()

    // Register the type of an expression in the typeMap.
    // Think of this as a type annotation.
    def e[E <: QuintEx](exp: E, typ: QuintType): E = {
      typeMap += (exp.id -> typ)
      exp
    }

    // Operator application
    def app(name: String, args: QuintEx*)(retType: QuintType): QuintApp = {
      e(QuintApp(uid, name, args), retType)
    }

    def param(name: String, typ: QuintType): QuintLambdaParameter = {
      val id = uid
      typeMap += (id -> typ)
      QuintLambdaParameter(id, name)
    }

    // Scalar values
    val tt = e(QuintBool(uid, true), QuintBoolT())
    val _0 = e(QuintInt(uid, 0), QuintIntT())
    val _1 = e(QuintInt(uid, 1), QuintIntT())
    val _2 = e(QuintInt(uid, 2), QuintIntT())
    val _3 = e(QuintInt(uid, 3), QuintIntT())
    val _42 = e(QuintInt(uid, 42), QuintIntT())
    val s = e(QuintStr(uid, "s"), QuintStrT())
    val t = e(QuintStr(uid, "t"), QuintStrT())

    // Names and parameters
    val name = e(QuintName(uid, "n"), QuintIntT())
    val nParam = param("n", QuintIntT())
    val acc = e(QuintName(uid, "acc"), QuintIntT())
    val accParam = param("acc", QuintIntT())
    val xParam = param("x", QuintIntT())
    val namedIntToBoolOp = e(QuintName(uid, "intToBoolOp"), QuintOperT(Seq(QuintIntT()), QuintBoolT()))
    val namedInt2ToBoolOp = e(QuintName(uid, "int2ToBoolOp"), QuintOperT(Seq(QuintIntT(), QuintIntT()), QuintBoolT()))

    // Definitions and compound data types
    val fooDef = QuintDef.QuintOpDef(uid, "foo", "val", tt)
    val letFooBeTrueIn42 = e(QuintLet(uid, fooDef, _42), QuintIntT())
    val lambda = e(QuintLambda(uid, List(xParam), "def", s), QuintOperT(List(QuintIntT()), QuintStrT()))
    // Applications can only be by name (lambdas are not first class)
    val barDef = QuintDef.QuintOpDef(uid, "bar", "def", lambda)
    val appBar = app("bar", _42)(QuintStrT())
    val letBarBeLambdaInAppBar = e(QuintLet(uid, barDef, appBar), QuintStrT())
    val nIsGreaterThan0 = app("igt", name, _0)(QuintBoolT())
    val nDefindedAs42 = QuintDef.QuintOpDef(uid, "n", "val", _42)
    val letNbe42inNisGreaterThan0 = e(QuintLet(uid, nDefindedAs42, nIsGreaterThan0), QuintBoolT())
    // A predicate on ints
    val intIsGreaterThanZero =
      e(QuintLambda(uid, List(nParam), "def", nIsGreaterThan0), QuintOperT(List(QuintIntT()), QuintBoolT()))
    val int2ToBool =
      e(QuintLambda(uid, List(nParam, accParam), "def", tt), QuintOperT(List(QuintIntT(), QuintIntT()), QuintBoolT()))
    val intSet = app("Set", _1, _2, _3)(QuintSetT(QuintIntT()))
    val intPair = app("Tup", _1, _2)(QuintTupleT.ofTypes(QuintIntT(), QuintIntT()))
    val intList = app("List", _1, _2, _3)(QuintSeqT(QuintIntT()))
    val intPairSet = app("Set", intPair, intPair)(QuintSetT(QuintTupleT.ofTypes(QuintIntT())))
    val emptyIntList = app("List")(QuintSeqT(QuintIntT()))
    val emptyIntSet = app("Set")(QuintSetT(QuintIntT()))
    val setOfIntSets = app("Set", intSet, intSet, intSet)(QuintSetT(QuintSetT(QuintIntT())))
    val intTup1 = app("Tup", _0, _1)(QuintTupleT.ofTypes(QuintIntT(), QuintIntT()))
    val intTup2 = app("Tup", _3, _42)(QuintTupleT.ofTypes(QuintIntT(), QuintIntT()))
    val intMap = app("Map", intTup1, intTup2)(QuintFunT(QuintIntT(), QuintIntT())) // Map(0 -> 1, 3 -> 42)
    // For use in folds
    val addNameAndAcc = app("iadd", name, acc)(QuintIntT())
    val accumulatingOpp = e(QuintLambda(uid, List(accParam, nParam), "def", addNameAndAcc),
        QuintOperT(List(QuintIntT(), QuintIntT()), QuintIntT()))
    val chooseSomeFromIntSet = app("chooseSome", intSet)(QuintIntT())
    val oneOfSet = app("oneOf", intSet)(QuintIntT())
    val nondetBinding =
      e(QuintLet(uid, QuintDef.QuintOpDef(uid, "n", "nondet", oneOfSet), nIsGreaterThan0), QuintIntT())
    // Requires ID registered with type
    val selectGreaterThanZero = app("select", intList, intIsGreaterThanZero)(QuintSeqT(QuintIntT()))
    val addOne = app("iadd", name, _1)(QuintIntT())
    val addOneOp = e(QuintLambda(uid, List(nParam), "def", addOne), QuintOperT(List(QuintIntT()), QuintIntT()))
    val setByExpression = app("setBy", intMap, _1, addOneOp)(QuintFunT(QuintIntT(), QuintIntT()))
    val selectNamedIntToBoolOp = app("select", intList, namedIntToBoolOp)(QuintSeqT(QuintIntT()))
    val applyNamedIntToBoolOp = app(namedIntToBoolOp.name, _42, _42)(QuintBoolT())

    // We construct a converter supplied with the needed type map
    def quint = new Quint(QuintOutput(
            "typechecking",
            List(QuintModule(0, "MockedModule", List())),
            typeMap.map { case (id, typ) =>
              // Wrap each type in the TypeScheme required by the Quint IR
              id -> QuintTypeScheme(typ)
            }.toMap,
        ))

  }

  // Convert a quint expression to TLA and render as a string
  def convert(qex: QuintEx): String = {
    Q.quint.exToTla(qex).get.toString()
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
    assert(convert(Q.app("eq", Q.tt, Q.tt)(QuintBoolT())) == "TRUE = TRUE")
  }

  test("can convert builtin neq operator application") {
    assert(convert(Q.app("neq", Q.tt, Q.tt)(QuintBoolT())) == "TRUE ≠ TRUE")
  }

  test("can convert builtin iff operator application") {
    assert(convert(Q.app("iff", Q.tt, Q.tt)(QuintBoolT())) == "TRUE ⇔ TRUE")
  }

  test("can convert builtin implies operator application") {
    assert(convert(Q.app("implies", Q.tt, Q.tt)(QuintBoolT())) == "TRUE ⇒ TRUE")
  }

  test("can convert builtin not operator application") {
    assert(convert(Q.app("not", Q.tt)(QuintBoolT())) == "¬TRUE")
  }

  test("can convert builtin and operator application") {
    assert(convert(Q.app("and", Q.tt, Q.tt)(QuintBoolT())) == "TRUE ∧ TRUE")
  }

  test("can convert builtin or operator application") {
    assert(convert(Q.app("or", Q.tt, Q.tt)(QuintBoolT())) == "TRUE ∨ TRUE")
  }

  // Integers
  test("can convert builtin iadd operator application") {
    assert(convert(Q.app("iadd", Q._42, Q._42)(QuintIntT())) == "42 + 42")
  }

  test("can convert builtin isub operator application") {
    assert(convert(Q.app("isub", Q._42, Q._42)(QuintIntT())) == "42 - 42")
  }

  test("can convert builtin imul operator application") {
    assert(convert(Q.app("imul", Q._42, Q._42)(QuintIntT())) == "42 * 42")
  }

  test("can convert builtin idiv operator application") {
    assert(convert(Q.app("idiv", Q._42, Q._42)(QuintIntT())) == "42 // 42")
  }

  test("can convert builtin imod operator application") {
    assert(convert(Q.app("imod", Q._42, Q._42)(QuintIntT())) == "42 % 42")
  }

  test("can convert builtin ipow operator application") {
    assert(convert(Q.app("ipow", Q._42, Q._42)(QuintIntT())) == "42 ^ 42")
  }

  test("can convert builtin ilt operator application") {
    assert(convert(Q.app("ilt", Q._42, Q._42)(QuintBoolT())) == "42 < 42")
  }

  test("can convert builtin igt operator application") {
    assert(convert(Q.app("igt", Q._42, Q._42)(QuintBoolT())) == "42 > 42")
  }

  test("can convert builtin ilte operator application") {
    assert(convert(Q.app("ilte", Q._42, Q._42)(QuintBoolT())) == "42 ≤ 42")
  }

  test("can convert builtin igte operator application") {
    assert(convert(Q.app("igte", Q._42, Q._42)(QuintBoolT())) == "42 ≥ 42")
  }

  test("can convert builtin iuminus operator application") {
    assert(convert(Q.app("iuminus", Q._42)(QuintBoolT())) == "-42")
  }

  test("can convert builtin Set operator application") {
    assert(convert(Q.app("Set", Q.s, Q.s, Q.s)(QuintSetT(QuintStrT()))) == """{"s", "s", "s"}""")
  }

  test("can convert builtin Set operator application for empty sets") {
    val tlaEx = Q.quint.exToTla(Q.emptyIntSet).get
    // Ensure the constructed empty set has the required type
    assert(tlaEx.typeTag match {
      case Typed(SetT1(IntT1)) => true
      case _                   => false
    })
    assert(tlaEx.toString() == """{}""")
  }

  test("can convert builtin exists operator application") {
    assert(convert(Q.app("exists", Q.intSet, Q.intIsGreaterThanZero)(QuintBoolT())) == "∃n ∈ {1, 2, 3}: (n > 0)")
  }

  test("can convert builtin exists operator application using tuple-bound names") {
    assert(convert(Q.app("exists", Q.intPairSet, Q.int2ToBool)(
            QuintBoolT())) == "∃(<<n, acc>>) ∈ {<<1, 2>>, <<1, 2>>}: TRUE")
  }

  test("can convert builtin exists operator when predicate is supplied by name") {
    assert(convert(Q.app("exists", Q.intSet, Q.namedIntToBoolOp)(
            QuintBoolT())) == "∃__quint_var0 ∈ {1, 2, 3}: (intToBoolOp(__quint_var0))")
  }

  test("can convert builtin exists operator when multi-arity predicate is supplied by name") {
    assert(convert(Q.app("exists", Q.intPairSet, Q.namedInt2ToBoolOp)(QuintBoolT()))
      ==
        "∃(<<__quint_var0, __quint_var1>>) ∈ {<<1, 2>>, <<1, 2>>}: (int2ToBoolOp(__quint_var0, __quint_var1))")
  }

  test("can convert builtin forall operator application") {
    assert(convert(Q.app("forall", Q.intSet, Q.intIsGreaterThanZero)(QuintBoolT())) == "∀n ∈ {1, 2, 3}: (n > 0)")
  }

  test("can convert builtin forall operator application using tuple-bound names") {
    assert(convert(Q.app("forall", Q.intPairSet, Q.int2ToBool)(
            QuintBoolT())) == "∀(<<n, acc>>) ∈ {<<1, 2>>, <<1, 2>>}: TRUE")
  }

  test("can convert builtin forall operator when predicate is supplied by name") {
    assert(convert(Q.app("forall", Q.intSet, Q.namedIntToBoolOp)(
            QuintBoolT())) == "∀__quint_var0 ∈ {1, 2, 3}: (intToBoolOp(__quint_var0))")
  }

  test("can convert builtin forall operator when multi-arity predicate is supplied by name") {
    assert(convert(Q.app("forall", Q.intPairSet, Q.namedInt2ToBoolOp)(QuintBoolT()))
      ==
        "∀(<<__quint_var0, __quint_var1>>) ∈ {<<1, 2>>, <<1, 2>>}: (int2ToBoolOp(__quint_var0, __quint_var1))")
  }

  test("converting binary binding operator with missing lambda fails") {
    val exn = intercept[QuintIRParseError] {
      convert(Q.app("forall", Q.intSet, Q.intSet)(QuintBoolT()))
    }
    assert(exn.getMessage.contains(
            "Input was not a valid representation of the QuintIR: Operator forall is a binding operator requiring an operator as it's second argument"))
  }

  test("converting binary binding operator with invalid arity fails") {
    val exn = intercept[QuintIRParseError] {
      convert(Q.app("forall", Q.intSet)(QuintBoolT()))
    }
    assert(exn.getMessage.contains(
            "Input was not a valid representation of the QuintIR: too many arguments passed to binary operator forall"))
  }

  test("can convert builtin in operator application") {
    assert(convert(Q.app("in", Q._1, Q.intSet)(QuintBoolT())) == "1 ∈ {1, 2, 3}")
  }

  test("can convert builtin contains operator application") {
    assert(convert(Q.app("contains", Q.intSet, Q._1)(QuintBoolT())) == "1 ∈ {1, 2, 3}")
  }

  test("can convert builtin notin operator application") {
    assert(convert(Q.app("notin", Q._1, Q.intSet)(QuintBoolT())) == "1 ∉ {1, 2, 3}")
  }

  test("can convert builtin union operator application") {
    assert(convert(Q.app("union", Q.intSet, Q.intSet)(QuintSetT(QuintIntT()))) == "{1, 2, 3} ∪ {1, 2, 3}")
  }

  test("can convert builtin intersect operator application") {
    assert(convert(Q.app("intersect", Q.intSet, Q.intSet)(QuintSetT(QuintIntT()))) == "{1, 2, 3} ∩ {1, 2, 3}")
  }

  test("can convert builtin exclude operator application") {
    assert(convert(Q.app("exclude", Q.intSet, Q.intSet)(QuintSetT(QuintIntT()))) == "{1, 2, 3} ∖ {1, 2, 3}")
  }

  test("can convert builtin subseteq operator application") {
    assert(convert(Q.app("subseteq", Q.intSet, Q.intSet)(QuintBoolT())) == "{1, 2, 3} ⊆ {1, 2, 3}")
  }

  test("can convert builtin filter operator application") {
    assert(convert(Q.app("filter", Q.intSet, Q.intIsGreaterThanZero)(
            QuintSetT(QuintIntT()))) == "{n ∈ {1, 2, 3}: (n > 0)}")
  }

  test("can convert builtin map operator application") {
    assert(convert(Q.app("map", Q.intSet, Q.intIsGreaterThanZero)(QuintSetT(QuintIntT()))) == "{n > 0 : n ∈ {1, 2, 3}}")
  }

  test("can convert builtin fold operator application") {
    val expected = "Apalache!ApaFoldSet(LET __QUINT_LAMBDA0(acc, n) ≜ n + acc IN __QUINT_LAMBDA0, 1, {1, 2, 3})"
    assert(convert(Q.app("fold", Q.intSet, Q._1, Q.accumulatingOpp)(QuintIntT())) == expected)
  }

  test("can convert builtin powerset operator application") {
    assert(convert(Q.app("powerset", Q.intSet)(QuintSetT(QuintSetT(QuintIntT())))) == "SUBSET {1, 2, 3}")
  }

  test("can convert builtin flatten operator application") {
    assert(convert(Q.app("flatten", Q.setOfIntSets)(
            QuintSetT(QuintIntT()))) == "UNION {{1, 2, 3}, {1, 2, 3}, {1, 2, 3}}")
  }

  test("can convert builtin allLists operator application") {
    assert(convert(Q.app("allLists", Q.intSet)(QuintSetT(QuintSeqT(QuintIntT())))) == "Seq({1, 2, 3})")
  }

  test("can convert builtin chooseSome operator application") {
    assert(convert(Q.chooseSomeFromIntSet) == "CHOOSE __quint_var0 ∈ {1, 2, 3} : TRUE")
  }

  test("can convert builtin isFinite operator application") {
    assert(convert(Q.app("isFinite", Q.intSet)(QuintBoolT())) == "IsFiniteSet({1, 2, 3})")
  }

  test("can convert builtin size operator application") {
    assert(convert(Q.app("size", Q.intSet)(QuintIntT())) == "Cardinality({1, 2, 3})")
  }

  test("can convert builtin to operator application") {
    assert(convert(Q.app("to", Q._1, Q._42)(QuintSetT(QuintIntT()))) == "1 .. 42")
  }

  test("can convert builtin List operator application") {
    assert(convert(Q.app("List", Q._1, Q._2, Q._3)(QuintSeqT(QuintIntT()))) == "<<1, 2, 3>>")
  }

  test("can convert builtin List operator application for empty list") {
    assert(convert(Q.emptyIntList) == "<<>>")
  }

  test("can convert builtin append operator application") {
    assert(convert(Q.app("append", Q.intList, Q._42)(QuintSeqT(QuintIntT()))) == "Append(<<1, 2, 3>>, 42)")
  }

  test("can convert builtin concat operator application") {
    assert(convert(Q.app("concat", Q.intList, Q.intList)(QuintSeqT(QuintIntT()))) == "(<<1, 2, 3>>) ∘ (<<1, 2, 3>>)")
  }

  test("can convert builtin head operator application") {
    assert(convert(Q.app("head", Q.intList)(QuintIntT())) == "Head(<<1, 2, 3>>)")
  }

  test("can convert builtin tail operator application") {
    assert(convert(Q.app("tail", Q.intList)(QuintSeqT(QuintIntT()))) == "Tail(<<1, 2, 3>>)")
  }

  test("can convert builtin length operator application") {
    assert(convert(Q.app("length", Q.intList)(QuintIntT())) == "Len(<<1, 2, 3>>)")
  }

  test("can convert builtin indices operator application") {
    val expected =
      "LET __quint_var0 ≜ DOMAIN (<<1, 2, 3>>) IN IF (__quint_var0() = {}) THEN {} ELSE ((__quint_var0() ∪ {0}) ∖ {Len(<<1, 2, 3>>)})"
    assert(convert(Q.app("indices", Q.intList)(QuintSetT(QuintIntT()))) == expected)
  }

  test("can convert builtin foldl operator application") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA0(acc, n) ≜ n + acc IN __QUINT_LAMBDA0, 0, <<1, 2, 3>>)"
    assert(convert(Q.app("foldl", Q.intList, Q._0, Q.accumulatingOpp)(QuintSeqT(QuintIntT()))) == expected)
  }

  test("can convert builtin nth operator application") {
    assert(convert(Q.app("nth", Q.intList, Q._1)(QuintIntT())) == "(<<1, 2, 3>>)[1 + 1]")
  }

  test("can convert builtin nth operator application to variable index") {
    assert(convert(Q.app("nth", Q.intList, Q.name)(QuintIntT())) == "(<<1, 2, 3>>)[n + 1]")
  }

  test("can convert builtin replaceAt operator application") {
    assert(convert(Q.app("replaceAt", Q.intList, Q._1, Q._42)(
            QuintSeqT(QuintIntT()))) == "[<<1, 2, 3>> EXCEPT ![<<1 + 1>>] = 42]")
  }

  test("can convert builtin slice operator application") {
    assert(convert(Q.app("slice", Q.intList, Q._0, Q._1)(
            QuintSeqT(QuintIntT()))) == "Sequences!SubSeq(<<1, 2, 3>>, 0 + 1, 1 + 1)")
  }

  test("can convert builtin select operator application") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA0(__quint_var0, n) ≜ IF (n > 0) THEN (Append(__quint_var0, n)) ELSE __quint_var0 IN __QUINT_LAMBDA0, <<>>, <<1, 2, 3>>)"
    assert(convert(Q.selectGreaterThanZero) == expected)
  }

  test("can convert builtin select operator application with named test operator") {
    val expected =
      "Apalache!ApaFoldSeqLeft(LET __QUINT_LAMBDA0(__quint_var1, __quint_var0) ≜ IF (intToBoolOp(__quint_var0)) THEN (Append(__quint_var1, __quint_var0)) ELSE __quint_var1 IN __QUINT_LAMBDA0, <<>>, <<1, 2, 3>>)"
    assert(convert(Q.selectNamedIntToBoolOp) == expected)
  }

  test("can convert builtin range operator application") {
    assert(convert(Q.app("range", Q._3, Q._42)(
            QuintSeqT(QuintIntT()))) == "Apalache!MkSeq(42 - 3, LET __QUINT_LAMBDA0(__quint_var0) ≜ (3 + __quint_var0) - 1 IN __QUINT_LAMBDA0)")
  }

  test("can convert builtin Rec operator application") {
    val typ = QuintRecordT.ofFieldTypes(("s", QuintIntT()), ("t", QuintIntT()))
    assert(convert(Q.app("Rec", Q.s, Q._1, Q.t, Q._2)(typ)) == """["s" ↦ 1, "t" ↦ 2]""")
  }

  test("convert builtin Rec operator constructing empty record fails") {
    val exn = intercept[QuintUnsupportedError] {
      val typ = QuintRecordT.ofFieldTypes(("s", QuintIntT()), ("t", QuintIntT()))
      convert(Q.app("Rec")(typ))
    }
    assert(exn.getMessage.contains(
            "Unsupported quint input: Given empty record, but Apalache doesn't support empty records."))
  }

  test("can convert builtin field operator application") {
    val rec = {
      val typ = QuintRecordT.ofFieldTypes(("s", QuintIntT()), ("t", QuintIntT()))
      Q.app("Rec", Q.s, Q._1, Q.t, Q._2)(typ)
    }
    assert(convert(Q.app("field", rec, Q.s)(QuintIntT())) == """(["s" ↦ 1, "t" ↦ 2])["s"]""")
  }

  test("can convert builtin fieldNames operator application") {
    val rec = {
      val typ = QuintRecordT.ofFieldTypes(("s", QuintIntT()), ("t", QuintIntT()))
      Q.app("Rec", Q.s, Q._1, Q.t, Q._2)(typ)
    }
    assert(convert(Q.app("fieldNames", rec)(QuintSetT(QuintStrT()))) == """DOMAIN (["s" ↦ 1, "t" ↦ 2])""")
  }

  test("can convert builtin with operator application") {
    val typ = QuintRecordT.ofFieldTypes(("s", QuintIntT()), ("t", QuintIntT()))
    val rec = Q.app("Rec", Q.s, Q._1, Q.t, Q._2)(typ)
    assert(convert(Q.app("with", rec, Q.s, Q._42)(typ)) == """[["s" ↦ 1, "t" ↦ 2] EXCEPT ![<<"s">>] = 42]""")
  }

  test("can convert builtin Tup operator application") {
    assert(convert(Q.app("Tup", Q._0, Q._1)(QuintTupleT.ofTypes(QuintIntT(), QuintIntT()))) == "<<0, 1>>")
  }

  test("can convert builtin Tup operator application to heterogeneous elements") {
    assert(convert(Q.app("Tup", Q._0, Q.s)(QuintTupleT.ofTypes(QuintStrT(), QuintStrT()))) == "<<0, \"s\">>")
  }

  test("can convert builtin item operator application") {
    assert(convert(Q.app("item", Q.intPair, Q._1)(QuintIntT())) == "(<<1, 2>>)[1]")
  }

  test("can convert builtin tuples operator application") {
    val typ = QuintSetT(QuintTupleT.ofTypes(QuintIntT(), QuintIntT(), QuintIntT()))
    assert(convert(Q.app("tuples", Q.intSet, Q.intSet, Q.intSet)(typ)) == "{1, 2, 3} × {1, 2, 3} × {1, 2, 3}")
  }

  test("can convert builtin assert operator") {
    assert(convert(Q.app("assert", Q.nIsGreaterThan0)(QuintBoolT())) == "n > 0")
  }

  test("can convert builtin Map operator") {
    assert(convert(Q.app("Map", Q.intTup1, Q.intTup2)(QuintFunT(QuintIntT(),
                QuintIntT()))) == "Apalache!SetAsFun({<<0, 1>>, <<3, 42>>})")
  }

  test("can convert builtin Map operator for empty maps") {
    assert(convert(Q.app("Map")(QuintFunT(QuintIntT(), QuintIntT()))) == "Apalache!SetAsFun({})")
  }

  test("can convert builtin get operator") {
    assert(convert(Q.app("get", Q.intMap, Q._0)(QuintIntT())) == "Apalache!SetAsFun({<<0, 1>>, <<3, 42>>})[0]")
  }

  test("can convert builtin keys operator") {
    assert(convert(Q.app("keys", Q.intMap)(
            QuintSetT(QuintIntT()))) == "DOMAIN Apalache!SetAsFun({<<0, 1>>, <<3, 42>>})")
  }

  test("can convert builtin setToMap operator") {
    assert(convert(Q.app("setToMap", Q.intPairSet)(QuintFunT(QuintIntT(),
                QuintIntT()))) == "Apalache!SetAsFun({<<1, 2>>, <<1, 2>>})")
  }

  val intMapT = QuintSetT(QuintFunT(QuintIntT(), QuintIntT()))

  test("can convert builtin setOfMaps operator") {
    assert(convert(Q.app("setOfMaps", Q.intSet, Q.intSet)(intMapT)) == "[{1, 2, 3} → {1, 2, 3}]")
  }

  test("can convert builtin set operator") {
    assert(
        convert(Q.app("set", Q.intMap, Q._3, Q._2)(intMapT))
          ==
            "[Apalache!SetAsFun({<<0, 1>>, <<3, 42>>}) EXCEPT ![<<3>>] = 2]"
    )
  }

  test("can convert builtin mapBy operator") {
    assert(convert(Q.app("mapBy", Q.intSet, Q.addOneOp)(intMapT)) == "[n ∈ {1, 2, 3} ↦ n + 1]")
  }

  test("can convert builtin setBy operator") {
    val expected = """
        |LET __quint_var0 ≜ Apalache!SetAsFun({<<0, 1>>, <<3, 42>>}) IN
        |[__quint_var0() EXCEPT ![<<1>>] = (LET __QUINT_LAMBDA0(n) ≜ n + 1 IN __QUINT_LAMBDA0(__quint_var0()[1]))]
        """.stripMargin.linesIterator.mkString(" ").trim
    assert(convert(Q.setByExpression) == expected)
  }

  test("can convert builtin put operator application") {
    val expected = """
        |LET __quint_var0 ≜ Apalache!SetAsFun({<<0, 1>>, <<3, 42>>}) IN
        |LET __quint_var1 ≜ DOMAIN __quint_var0() IN
        |[__quint_var2 ∈ ({3} ∪ __quint_var1()) ↦ IF (__quint_var2 = 3) THEN 42 ELSE __quint_var0()[__quint_var2]]
        """.stripMargin.linesIterator.mkString(" ").trim
    assert(convert(Q.app("put", Q.intMap, Q._3, Q._42)(intMapT)) == expected)
  }

  test("can convert nondet bindings") {
    assert(convert(Q.nondetBinding) == "∃n ∈ {1, 2, 3}: (n > 0)")
  }

  test("can convert let binding with reference to name in scope") {
    assert(convert(Q.letNbe42inNisGreaterThan0) == "LET n ≜ 42 IN n() > 0")
  }

  test("can convert application of defined operator") {
    assert(convert(Q.applyNamedIntToBoolOp) == "intToBoolOp(42, 42)")
  }

  test("can convert fail operator") {
    assert(convert(Q.app("fail", Q.tt)(QuintBoolT())) == "¬TRUE")
  }

  test("can convert next operator") {
    assert(convert(Q.app("next", Q.name)(QuintIntT())) == "n'")
  }

  test("can convert orKeep operator") {
    assert(convert(Q.app("orKeep", Q.tt, Q.name)(QuintBoolT())) == "[TRUE]_n")
  }

  test("can convert mustChange operator") {
    assert(convert(Q.app("mustChange", Q.tt, Q.name)(QuintBoolT())) == "<TRUE>_n")
  }

  test("can convert enabled operator") {
    assert(convert(Q.app("enabled", Q.tt)(QuintBoolT())) == "ENABLED TRUE")
  }

  test("can convert then operator") {
    assert(convert(Q.app("then", Q.tt, Q.tt)(QuintBoolT())) == "TRUE ⋅ TRUE")
  }

  test("cannot convert repeated operator") {
    val exn = intercept[QuintIRParseError] {
      convert(Q.app("repeated", Q.tt)(QuintBoolT()))
    }
    assert(exn.getMessage.contains("Operator 'repeated' is not supported"))
  }

  test("can convert always operator") {
    assert(convert(Q.app("always", Q.tt)(QuintBoolT())) == "☐TRUE")
  }

  test("can convert eventually operator") {
    assert(convert(Q.app("eventually", Q.tt)(QuintBoolT())) == "♢TRUE")
  }

  test("can convert weakFair operator") {
    assert(convert(Q.app("weakFair", Q.tt, Q.tt)(QuintBoolT())) == "WF_TRUE(TRUE)")
  }

  test("can convert strongFair operator") {
    assert(convert(Q.app("strongFair", Q.tt, Q.tt)(QuintBoolT())) == "SF_TRUE(TRUE)")
  }
}

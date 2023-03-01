package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import QuintType._
import QuintEx._

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

    val tt = QuintBool(uid, true)
    val _42 = QuintInt(uid, 42)
    val s = QuintStr(uid, "s")
    val name = QuintName(uid, "n")
    val fooDef = QuintDef.QuintOpDef(uid, "foo", "val", tt)
    val letFooBeTrueIn42 = QuintLet(uid, fooDef, _42)
    val lambda = QuintLambda(uid, List("x"), "def", s)
    // Applications can only be by name (lambdas are not first class)
    val barDef = QuintDef.QuintOpDef(uid, "bar", "def", lambda)
    val appBar = QuintApp(uid, "bar", List(_42))
    val letBarBeLambdaInAppBar = QuintLet(uid, barDef, appBar)

    // Builtin operator application
    def app(name: String, args: QuintEx*): QuintApp = QuintApp(uid, name, args)
  }

  // The Quint conversion class requires a QuintOutput object which,
  // to enable expression conversion, requires a correctly constructed
  // map of expression IDs to their inferred and checked types.
  val typeMapping: Map[QuintEx, QuintType] = Map(
      Q.tt -> QuintBoolT(),
      Q._42 -> QuintIntT(),
      Q.s -> QuintStrT(),
      Q.name -> QuintIntT(),
      Q.letFooBeTrueIn42 -> QuintBoolT(),
      Q.lambda -> QuintOperT(List(QuintIntT()), QuintStrT()),
      Q.appBar -> QuintStrT(),
      Q.letBarBeLambdaInAppBar -> QuintStrT(),
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
}

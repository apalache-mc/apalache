package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import QuintType._
import QuintEx._
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.LetInEx
import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.OperParam
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.OperEx

/**
 * Tests the conversion of quint expressions and declarations into TLA expressions
 */
@RunWith(classOf[JUnitRunner])
class TestQuintEx extends AnyFunSuite {

  // Quint expressions used in the unit tests
  // expression IDs must be unique
  object Q {
    val bool = QuintBool(1, true)
    val int = QuintInt(2, 42)
    val str = QuintStr(3, "s")
    val name = QuintName(4, "n")
    val fooDef = QuintDef.QuintOpDef(5, "foo", "val", bool)
    val letFooBeTrueIn42 = QuintLet(6, fooDef, int)
    val lambda = QuintLambda(7, List("x"), "def", str)
    // Applications can only be by name (lambdas are not first class)
    val barDef = QuintDef.QuintOpDef(8, "bar", "def", lambda)
    val appBar = QuintApp(9, "bar", List(int))
    val letBarBeLambdaInAppBar = QuintLet(10, barDef, appBar)
  }

  // The Quint conversion class requires a QuintOutput object which,
  // to enable expression conversion, requires a correctly constructed
  // map of expression IDs to their inferred and checked types.
  val typeMapping: Map[QuintEx, QuintType] = Map(
      Q.bool -> QuintBoolT(),
      Q.int -> QuintIntT(),
      Q.str -> QuintStrT(),
      Q.name -> QuintIntT(),
      Q.letFooBeTrueIn42 -> QuintBoolT(),
      Q.lambda -> QuintOperT(List(QuintIntT()), QuintStrT()),
      Q.appBar -> QuintStrT(),
      Q.letBarBeLambdaInAppBar -> QuintStrT(),
  )

  // We construct a converter supplied with the needed type map
  val quint = new Quint(QuintOutput(
          "typechecking",
          QuintModule(0, "MockedModule", List()),
          typeMapping.map { case (ex, typ) =>
            // Wrap each type in the TypeScheme required by the Quint IR
            ex.id -> QuintTypeScheme(typ)
          },
      ))

  test("can convert boolean") {
    val actual = quint.exToTla(Q.bool).get
    val expected = ValEx(TlaBool(true))
    assert(actual == expected)
  }

  test("can convert int") {
    val actual = quint.exToTla(Q.int).get
    val expected = ValEx(TlaInt(42))
    assert(actual == expected)
  }

  test("can convert str") {
    val actual = quint.exToTla(Q.str).get
    val expected = ValEx(TlaStr("s"))
    assert(actual == expected)
  }

  test("can convert name") {
    val actual = quint.exToTla(Q.name).get
    val expected = NameEx("n")
    assert(actual == expected)
  }

  test("can convert let expression") {
    val actual = quint.exToTla(Q.letFooBeTrueIn42).get
    val expected = LetInEx(ValEx(TlaInt(42)), TlaOperDecl("foo", List(), ValEx(TlaBool(true))))
    assert(actual == expected)
  }

  test("can convert lambda") {
    val actual = quint.exToTla(Q.lambda).get
    val expected =
      LetInEx(
          NameEx("__QUINT_LAMBDA0"),
          TlaOperDecl("__QUINT_LAMBDA0", List(OperParam("x")), ValEx(TlaStr("s"))),
      )
    assert(actual == expected)
  }

  test("can convert operator application") {
    val actual = quint.exToTla(Q.letBarBeLambdaInAppBar).get
    val expected =
      LetInEx(OperEx(TlaOper.apply, NameEx("bar"), ValEx(TlaInt(42))),
          TlaOperDecl("bar", List(OperParam("x")), ValEx(TlaStr("s"))))
    assert(actual == expected)
  }
}

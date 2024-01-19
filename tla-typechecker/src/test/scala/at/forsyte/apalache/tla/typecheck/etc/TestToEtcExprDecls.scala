package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.types.parser.{DefaultType1Parser, Type1Parser}
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

/**
 * Unit tests for translating declarations rather than single expressions.
 *
 * @author
 *   Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestToEtcExprDecls extends AnyFunSuite with ToEtcExprBase with BeforeAndAfterEach with EtcBuilder {
  var parser: Type1Parser = DefaultType1Parser

  test("An operator declaration with a java-like annotation") {
    // translating the definition
    // \* @type: Int => Bool;
    // Positive(x) ==
    //   x > 0
    val cmp = tla.lt(tla.name("x"), tla.int(0))
    // "be like a proton, always positive"
    val positive = TlaOperDecl("Positive", List(OperParam("x")), cmp)

    // becomes:
    // Foo: (Int => Bool) in
    //   let Foo = λ x ∈ Set(a). ((Int, Int) => Bool) x Int in
    //   Bool // the terminal expression
    val defBody = mkUniqApp(Seq(parser("((Int, Int) => Bool)")), mkUniqName("x"), mkUniqConst(parser("Int")))
    val positiveLambda = mkUniqAbs(defBody, (mkUniqName("x"), mkUniqConst(SetT1(VarT1("a")))))
    val positiveLet = mkUniqLet("Positive", positiveLambda, mkUniqConst(BoolT1))
    val expected = mkUniqTypeDecl("Positive", parser("Int => Bool"), positiveLet)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == mkToEtcExpr(Map(positive.ID -> parser("Int => Bool")))(positive, mkUniqConst(BoolT1)))
  }

  test("constant declarations with java-like annotations") {
    // CONSTANT N
    val constDecl = TlaConstDecl("N")
    // @type: Int;
    val annotations = Map(constDecl.ID -> parser("Int"))

    val terminal = mkUniqConst(BoolT1)
    // becomes:
    // N: Int in
    // Bool // the terminal expression
    val expected = mkUniqTypeDecl("N", parser("Int"), terminal)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == mkToEtcExpr(annotations)(constDecl, mkUniqConst(BoolT1)))
  }

  test("variable declarations with java-like annotations") {
    // VARIABLE set
    val varDecl = TlaVarDecl("set")
    // @type: Set(Int);
    val annotations = Map(varDecl.ID -> parser("Set(Str)"))

    val terminal = mkUniqConst(BoolT1)
    // becomes:
    // set: Set(Str) in
    // Bool // the terminal expression
    val expected = mkUniqTypeDecl("set", parser("Set(Str)"), terminal)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == mkToEtcExpr(annotations)(varDecl, mkUniqConst(BoolT1)))
  }

  test("variable declarations with java-like annotations and aliases") {
    val aliases = TypeAliasSubstitution(Map("ENTRY" -> IntT1))
    // redefine gen to use aliases

    /*
        VARIABLES
           \* @typeAlias: ENTRY = Int;
           \* @type: ENTRY;
           entry,
           \* @type: Set(ENTRY);
           set
     */
    val entryDecl = TlaVarDecl("entry")
    val setDecl = TlaVarDecl("set")
    val annotations = Map(
        // @type: entry;
        entryDecl.ID -> parser("ENTRY"),
        // @type: Set(entry);
        setDecl.ID -> parser("Set(ENTRY)"),
    ) ///

    val terminal = mkUniqConst(BoolT1)
    // becomes:
    // set: Set(Int) in
    // Bool // the terminal expression
    val expected =
      mkUniqTypeDecl("entry", parser("Int"), mkUniqTypeDecl("set", parser("Set(Int)"), terminal))
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    def gen() = mkToEtcExpr(annotations, aliases)
    assert(expected == gen()(entryDecl, gen()(setDecl, terminal)))
  }

  test("assumes") {
    val assume = TlaAssumeDecl(None, tla.name("x"))
    val terminal = mkUniqConst(BoolT1)
    // becomes:
    // let Assume1 == ((Bool => Bool) "x") in
    // Bool // the terminal expression
    val assumption = mkUniqName("x")
    // The body is wrapped with the application of an operator that has the signature Bool => Bool.
    // This allows us to check that the assumption has Boolean type.
    val application = mkUniqApp(Seq(parser("Bool => Bool")), assumption)
    val expected =
      mkUniqLet("__Assume_" + assume.definedName.getOrElse(assume.ID.toString), mkUniqAbs(application), terminal)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == mkToEtcExpr(Map())(assume, terminal))
  }
}

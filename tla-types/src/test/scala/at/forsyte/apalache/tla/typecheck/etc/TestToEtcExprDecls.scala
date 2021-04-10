package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.io.annotations.StandardAnnotations
import at.forsyte.apalache.io.annotations.store.{AnnotationStore, createAnnotationStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

/**
 * Unit tests for translating declarations rather than single expressions.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestToEtcExprDecls extends FunSuite with BeforeAndAfterEach with EtcBuilder {
  var parser: Type1Parser = _
  var annotationStore: AnnotationStore = _
  var gen: ToEtcExpr = _

  override protected def beforeEach(): Unit = {
    parser = DefaultType1Parser
    annotationStore = createAnnotationStore()
    gen = new ToEtcExpr(annotationStore, ConstSubstitution.empty, new TypeVarPool())
  }

  test("An operator declaration with a java-like annotation") {
    // translating the definition
    // \* @type: Int => Bool;
    // Positive(x) ==
    //   x > 0
    val cmp = tla.lt(tla.name("x"), tla.int(0))
    // "be like a proton, always positive"
    val positive = TlaOperDecl("Positive", List(OperParam("x")), cmp)
    annotationStore += positive.ID -> List(StandardAnnotations.mkType("Int => Bool"))

    // becomes:
    // Foo: (Int => Bool) in
    //   let Foo = λ x ∈ Set(a). ((Int, Int) => Bool) x Int in
    //   Bool // the terminal expression
    val defBody = mkUniqApp(Seq(parser("((Int, Int) => Bool)")), mkUniqName("x"), mkUniqConst(parser("Int")))
    val positiveLambda = mkUniqAbs(defBody, (mkUniqName("x"), mkUniqConst(SetT1(VarT1("a")))))
    val positiveLet = mkUniqLet("Positive", positiveLambda, mkUniqConst(BoolT1()))
    val expected = mkUniqTypeDecl("Positive", parser("Int => Bool"), positiveLet)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(positive, mkUniqConst(BoolT1())))
  }

  test("constant declarations with java-like annotations") {
    // CONSTANT N
    val constDecl = TlaConstDecl("N")
    // @type: Int;
    annotationStore += constDecl.ID -> List(StandardAnnotations.mkType("Int"))

    val terminal = mkUniqConst(BoolT1())
    // becomes:
    // N: Int in
    // Bool // the terminal expression
    val expected = mkUniqTypeDecl("N", parser("Int"), terminal)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(constDecl, mkUniqConst(BoolT1())))
  }

  test("variable declarations with java-like annotations") {
    // VARIABLE set
    val varDecl = TlaVarDecl("set")
    // @type: Set(Int);
    annotationStore += varDecl.ID -> List(StandardAnnotations.mkType("Set(Str)"))

    val terminal = mkUniqConst(BoolT1())
    // becomes:
    // set: Set(Str) in
    // Bool // the terminal expression
    val expected = mkUniqTypeDecl("set", parser("Set(Str)"), terminal)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(varDecl, mkUniqConst(BoolT1())))
  }

  test("variable declarations with java-like annotations and aliases") {
    val aliases = ConstSubstitution(Map("ENTRY" -> IntT1()))
    // redefine gen to use aliases
    gen = new ToEtcExpr(annotationStore, aliases, new TypeVarPool())

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
    // @type: entry;
    annotationStore += entryDecl.ID -> List(StandardAnnotations.mkType("ENTRY"))
    // @type: Set(entry);
    annotationStore += setDecl.ID -> List(StandardAnnotations.mkType("Set(ENTRY)"))

    val terminal = mkUniqConst(BoolT1())
    // becomes:
    // set: Set(Int) in
    // Bool // the terminal expression
    val expected =
      mkUniqTypeDecl("entry", parser("Int"), mkUniqTypeDecl("set", parser("Set(Int)"), terminal))
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(entryDecl, gen(setDecl, terminal)))
  }

  test("assumes") {
    val assume = TlaAssumeDecl(tla.name("x"))
    val terminal = mkUniqConst(BoolT1())
    // becomes:
    // let Assume1 == ((Bool => Bool) "x") in
    // Bool // the terminal expression
    val assumption = mkUniqName("x")
    // The body is wrapped with the application of an operator that has the signature Bool => Bool.
    // This allows us to check that the assumption has Boolean type.
    val application = mkUniqApp(Seq(parser("Bool => Bool")), assumption)
    val expected = mkUniqLet("__Assume_" + assume.ID, mkUniqAbs(application), terminal)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(assume, terminal))
  }
}

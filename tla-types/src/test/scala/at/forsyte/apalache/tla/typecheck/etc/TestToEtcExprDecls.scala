package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TypingOper, TlaBoolOper}
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
class TestToEtcExprDecls
    extends FunSuite
    with BeforeAndAfterEach
    with EtcBuilder {
  var parser: Type1Parser = _
  var gen: ToEtcExpr = _

  override protected def beforeEach(): Unit = {
    parser = DefaultType1Parser
    gen = new ToEtcExpr(new TypeVarPool())
  }

  test("An annotated operator declaration") {
    // translating the definition
    // Positive(x) == "Int => Bool" :>
    //   x > 0
    val cmp = tla.lt(tla.name("x"), tla.int(0))
    val withType = OperEx(TypingOper.withType, tla.str("Int => Bool"), cmp)
    // "be like a proton, always positive"
    val positive =
      TlaOperDecl("Positive", List(SimpleFormalParam("x")), withType)

    // becomes:
    // Foo: (Int => Bool) in
    //   let Foo = λ x ∈ Set(a). ((Int, Int) => Bool) x Int in
    //   Bool // the terminal expression
    val defBody = mkUniqApp(
      Seq(parser("((Int, Int) => Bool)")),
      mkUniqName("x"),
      mkUniqConst(parser("Int"))
    )
    val positiveLambda =
      mkUniqAbs(defBody, ("x", mkUniqConst(SetT1(VarT1("a")))))
    val positiveLet =
      mkUniqLet("Positive", positiveLambda, mkUniqConst(BoolT1()))
    val expected =
      mkUniqTypeDecl("Positive", parser("Int => Bool"), positiveLet)
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(positive, mkUniqConst(BoolT1())))
  }

  test("declarations in TypeAssumptions") {
    // translating the definition
    // TypeAssumptions ==
    //   /\ AssumeType(x, "Int")
    //   /\ AssumeType(set, "Set(Str)")
    val assumeX = OperEx(TypingOper.assumeType, NameEx("x"), tla.str("Int"))
    val assumeSet =
      OperEx(TypingOper.assumeType, NameEx("set"), tla.str("Set(Str)"))
    val typeAssumptions =
      tla.declOp("TypeAssumptions", tla.and(assumeX, assumeSet))

    val terminal = mkUniqConst(BoolT1())
    // becomes:
    // x: Int in
    // set: Set(Str) in
    // Bool // the terminal expression
    val expected =
      mkUniqTypeDecl(
        "x",
        parser("Int"),
        mkUniqTypeDecl("set", parser("Set(Str)"), terminal)
      )
    // Translate the declaration of positive.
    // We have to pass the next expression in scope, which is just TRUE in this case.
    assert(expected == gen(typeAssumptions, mkUniqConst(BoolT1())))
  }

  test("invalid declarations in TypeAssumptions") {
    // translating the invalid TypeAssumption declaration
    // TypeAssumptions ==
    //   /\ AssumeType(x, "Int")
    //   /\ x <=> x  (* Invalid: should trigger error *)
    val assumeX = OperEx(TypingOper.assumeType, NameEx("x"), tla.str("Int"))
    val xEquivX = OperEx(TlaBoolOper.equiv, NameEx("x"), NameEx("x"))
    val typeAssumptions =
      tla.declOp("TypeAssumptions", tla.and(assumeX, xEquivX))

    val exn = intercept[TypingInputException](
      gen(typeAssumptions, mkUniqConst(BoolT1()))
    )
    // Ensure that the problematic expression is reported in the error
    assert(exn.getMessage.contains(xEquivX.toString))
  }

}

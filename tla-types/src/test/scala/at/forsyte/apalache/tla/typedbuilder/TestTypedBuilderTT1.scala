package at.forsyte.apalache.tla.typedbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTypedBuilderTT1 extends FunSuite {

  private val bd = new TypedBuilder(new TypeTag1Synthesizer)

  implicit def liftTT1(tt1: TlaType1): TypeTag = Typed(tt1)

  implicit val untyped: TypeTag = Untyped()

  def assertType[T](typed: TypeTagged[T], tt1: TlaType1): Unit =
    assert(typed.typeTag == Typed(tt1))

  def declToNameEx(d: TlaDecl): NameEx =
    bd.name(d.name, d.typeTag)

  test("Validation rejects Untyped()") {
    assertThrows[TypingException] {
      bd.name("a", Untyped())
    }
  }

  test("Test direct methods: Names and values") {
    val typeOfA: TypeTag = VarT1(0)
    val nameBuild: TlaEx = bd.name("a", typeOfA) // concrete type irrelevant

    assert(nameBuild == NameEx("a")(typeOfA))

    val vBigInt: BigInt = BigInt("1000000015943534656464398536")
    val vBigDecimal: BigDecimal = 1.111132454253626474876842798573504607
    val vBool: Boolean = false
    val vString: String = "a string val"

    val biBuild = bd.bigInt(vBigInt)
    val bdBuild = bd.decimal(vBigDecimal)
    val boolBuild = bd.bool(vBool)
    val strBuild = bd.str(vString)

    assert(biBuild == ValEx(TlaInt(vBigInt))(IntT1()))
    assert(bdBuild == ValEx(TlaDecimal(vBigDecimal))(RealT1()))
    assert(boolBuild == ValEx(TlaBool(vBool))(BoolT1()))
    assert(strBuild == ValEx(TlaStr(vString))(StrT1()))
  }

  test("Test direct methods: Declarations") {
    val resT = StrT1()
    // @type: Int;
    val xType = IntT1()
    val xParam = bd.simpleParam("x", xType)
    val xName = bd.name("x", xType)
    // @type: () => Str;
    val bType0 = OperT1(Seq.empty, StrT1())
    val bParam0 = bd.operParam("B", 0, bType0)
    val bName0 = bd.name("B", bType0)
    // @type: (Int) => Str;
    val bType1 = OperT1(Seq(xType), resT)
    val bParam1 = bd.operParam("B", 1, bType1)
    val bName1 = bd.name("B", bType1)
    // A == c
    val cName = bd.name("c", resT)
    val decl1 = bd.declOp("A", cName)
    // A(x) == x
    val decl2 = bd.declOp("A", xName, xParam)
    // A(B()) == B()
    val decl3 = bd.declOp("A", bd.appOp(bName0), bParam0)
    // A(x, B(_)) == B(x)
    val decl4 = bd.declOp("A", bd.appOp(bName1, xName), xParam, bParam1)

    assert(decl1 == TlaOperDecl("A", List(), cName))
    assertType(decl1, OperT1(Seq.empty, resT))
    assert(decl2 == TlaOperDecl("A", List(SimpleFormalParam("x")), xName))
    assertType(decl2, OperT1(Seq(xType), xType))
    assert(
        decl3 ==
          TlaOperDecl(
              "A",
              List(OperFormalParam("B", 0)),
              OperEx(TlaOper.apply, bName0)
          )
    )
    assertType(decl3.body, resT)
    assertType(decl3, OperT1(Seq(bType0), resT))
    assert(
        decl4 ==
          TlaOperDecl(
              "A",
              List(SimpleFormalParam("x"), OperFormalParam("B", 1)),
              OperEx(TlaOper.apply, bName1, xName)
          )
    )
    assertType(decl4.body, resT)
    assertType(decl4, OperT1(Seq(xType, bType1), resT))

    // A()
    val appEx1 = bd.appDecl(decl1)
    // A(a: Int)
    def a1 = bd.name("a", IntT1())
    val appEx2 = bd.appDecl(decl2, a1)
    // A(a: () => Str)
    def a2 = bd.name("a", OperT1(Seq.empty, StrT1()))
    val appEx3 = bd.appDecl(decl3, a2)
    // A(a: Int, B: (Int) => Str)
    def b = bd.name("b", OperT1(Seq(IntT1()), StrT1()))
    val appEx4 = bd.appDecl(decl4, a1, b)

    assert(appEx1 == OperEx(TlaOper.apply, declToNameEx(decl1)))
    assertType(appEx1, resT)
    assertThrows[IllegalArgumentException] {
      // applying arity 0 operator to 1 arg
      bd.appDecl(decl1, a1)
    }
    assertThrows[IllegalArgumentException] {
      // applying arity 1 operator to 0 args
      bd.appDecl(decl2)
    }
    assert(appEx2 == OperEx(TlaOper.apply, declToNameEx(decl2), a1))
    assertType(appEx2, xType)
    assertThrows[IllegalArgumentException] {
      bd.appDecl(decl2, a1, a2)
    }
    assertThrows[IllegalArgumentException] {
      bd.appDecl(decl3)
    }
    assert(appEx3 == OperEx(TlaOper.apply, declToNameEx(decl3), a1))
    assertType(appEx3, resT)
    assertThrows[IllegalArgumentException] {
      bd.appDecl(decl3, a1, a2)
    }
    assertThrows[IllegalArgumentException] {
      bd.appDecl(decl4)
    }
    assertThrows[IllegalArgumentException] {
      bd.appDecl(decl4, a1)
    }
    assert(appEx4 == OperEx(TlaOper.apply, declToNameEx(decl4), a1, b))
    assertType(appEx4, resT)
    assertThrows[IllegalArgumentException] {
      bd.appDecl(decl4, a1, b, a2)
    }
  }

//  test("Test direct methods: TlaOper") {
//    // a = b
//    val eqBuild1 = bd.eql(n_a, n_b)
//    val eqBuild2 = bd.eql(n_a, bd.int(2))
//
//    assert(eqBuild1 == OperEx(TlaOper.eq, n_a, n_b))
//    assert(eqBuild2 == OperEx(TlaOper.eq, n_a, ValEx(TlaInt(2))))
//
//    val neBuild1 = bd.neql(n_a, n_b)
//    val neBuild2 = bd.neql(n_a, bd.int(2))
//
//    assert(neBuild1 == OperEx(TlaOper.ne, n_a, n_b))
//    assert(neBuild2 == OperEx(TlaOper.ne, n_a, ValEx(TlaInt(2))))
//
//    val applyBuild1 = bd.appOp(n_a)
//    val applyBuild2 = bd.appOp(n_a, n_b)
//    val applyBuild3 = bd.appOp(n_a, n_b, n_c)
//    val applyBuild4 = bd.appOp(n_a, n_b, n_c, n_d)
//
//    assert(applyBuild1 == OperEx(TlaOper.apply, n_a))
//    assert(applyBuild2 == OperEx(TlaOper.apply, n_a, n_b))
//    assert(applyBuild3 == OperEx(TlaOper.apply, n_a, n_b, n_c))
//    assert(applyBuild4 == OperEx(TlaOper.apply, n_a, n_b, n_c, n_d))
//
//    val chooseBuild1 = bd.choose(n_a, n_b)
//    val chooseBuild2 = bd.choose(n_a, n_b, n_c)
//
//    assert(chooseBuild1 == OperEx(TlaOper.chooseUnbounded, n_a, n_b))
//    assert(chooseBuild2 == OperEx(TlaOper.chooseBounded, n_a, n_b, n_c))
//  }
//
//  test("Test direct methods: TlaBoolOper ") {
//    val andBuild1 = bd.and(n_a)
//    val andBuild2 = bd.and(n_a, n_b)
//    val andBuild3 = bd.and(n_a, n_b, n_c)
//    val andBuild4 = bd.and(n_a, n_b, n_c, n_d)
//
//    assert(andBuild1 == OperEx(TlaBoolOper.and, n_a))
//    assert(andBuild2 == OperEx(TlaBoolOper.and, n_a, n_b))
//    assert(andBuild3 == OperEx(TlaBoolOper.and, n_a, n_b, n_c))
//    assert(andBuild4 == OperEx(TlaBoolOper.and, n_a, n_b, n_c, n_d))
//
//    val orBuild1 = bd.or(n_a)
//    val orBuild2 = bd.or(n_a, n_b)
//    val orBuild3 = bd.or(n_a, n_b, n_c)
//    val orBuild4 = bd.or(n_a, n_b, n_c, n_d)
//
//    assert(orBuild1 == OperEx(TlaBoolOper.or, n_a))
//    assert(orBuild2 == OperEx(TlaBoolOper.or, n_a, n_b))
//    assert(orBuild3 == OperEx(TlaBoolOper.or, n_a, n_b, n_c))
//    assert(orBuild4 == OperEx(TlaBoolOper.or, n_a, n_b, n_c, n_d))
//
//    val notBuild1 = bd.not(n_a)
//
//    assert(notBuild1 == OperEx(TlaBoolOper.not, n_a))
//
//    val impliesBuild1 = bd.impl(n_a, n_b)
//
//    assert(impliesBuild1 == OperEx(TlaBoolOper.implies, n_a, n_b))
//
//    val equivBuild1 = bd.equiv(n_a, n_b)
//
//    assert(equivBuild1 == OperEx(TlaBoolOper.equiv, n_a, n_b))
//
//    val forallBuild1 = bd.forall(n_a, n_b)
//    val forallBuild2 = bd.forall(n_a, n_b, n_c)
//
//    assert(forallBuild1 == OperEx(TlaBoolOper.forallUnbounded, n_a, n_b))
//    assert(forallBuild2 == OperEx(TlaBoolOper.forall, n_a, n_b, n_c))
//
//    val existsBuild1 = bd.exists(n_a, n_b)
//    val existsBuild2 = bd.exists(n_a, n_b, n_c)
//
//    assert(existsBuild1 == OperEx(TlaBoolOper.existsUnbounded, n_a, n_b))
//    assert(existsBuild2 == OperEx(TlaBoolOper.exists, n_a, n_b, n_c))
//  }
//
//  test("Test direct methods: TlaActionOper") {
//    val primeBuild1 = bd.prime(n_a)
//    val primeBuild2 = bd.prime(bd.name("name", Untyped()))
//
//    assert(primeBuild1 == OperEx(TlaActionOper.prime, n_a))
//    assert(primeBuild2 == OperEx(TlaActionOper.prime, NameEx("name")))
//
//    val primeEqBuild1 = bd.primeEq(bd.name("name", Untyped()), n_a)
//    val primeEqBuild2 = bd.primeEq(n_a, n_b)
//    val primeEqBuild3 = bd.primeEq(bd.name("name", Untyped()), bd.int(1))
//    val primeEqBuild4 = bd.primeEq(n_a, bd.int(2))
//    val primeEqBuild5 = bd.primeEq(bd.name("name1", Untyped()), bd.name("name2", Untyped()))
//
//    assert(primeEqBuild1 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name")), n_a))
//    assert(primeEqBuild2 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, n_a), n_b))
//    assert(primeEqBuild3 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name")), ValEx(TlaInt(1))))
//    assert(primeEqBuild4 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, n_a), ValEx(TlaInt(2))))
//    assert(primeEqBuild5 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name1")), NameEx("name2")))
//
//    val stutterBuild = bd.stutt(n_a, n_b)
//
//    assert(stutterBuild == OperEx(TlaActionOper.stutter, n_a, n_b))
//
//    val nostutterBuild = bd.nostutt(n_a, n_b)
//
//    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, n_a, n_b))
//
//    val enabledBuild = bd.enabled(n_a)
//
//    assert(enabledBuild == OperEx(TlaActionOper.enabled, n_a))
//
//    val unchangedBuild = bd.unchanged(n_a)
//
//    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, n_a))
//
//    val compositionBuild = bd.comp(n_a, n_b)
//
//    assert(compositionBuild == OperEx(TlaActionOper.composition, n_a, n_b))
//
//  }
//
//  test("Test direct methods: TlaControlOper") {
//
//    val caseBuild1 = bd.caseSplit(n_a, n_b)
//    val caseBuild2 = bd.caseOther(n_a, n_b, n_c)
//    val caseBuild3 = bd.caseSplit(n_a, n_b, n_c, n_d)
//    val caseBuild4 = bd.caseOther(n_a, n_b, n_c, n_d, n_e)
//    val caseBuild5 = bd.caseSplit(n_a, n_b, n_c, n_d, n_e, n_f)
//    val caseBuild6 = bd.caseOther(n_a, n_b, n_c, n_d, n_e, n_f, n_g)
//
//    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
//    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))
//    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d))
//    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e))
//    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f))
//    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g))
//
//    val caseSplitBuild1 = bd.caseSplit(n_a, n_b)
//    val caseSplitBuild2 = bd.caseSplit(n_a, n_b, n_c, n_d)
//    val caseSplitBuild3 = bd.caseSplit(n_a, n_b, n_c, n_d, n_e, n_f)
//
//    assert(caseSplitBuild1 == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
//    assertThrows[IllegalArgumentException](bd.caseSplit(n_a, n_b, n_c))
//    assert(caseSplitBuild2 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d))
//    assertThrows[IllegalArgumentException](bd.caseSplit(n_a, n_b, n_c, n_d, n_e))
//    assert(caseSplitBuild3 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f))
//
//    val caseOtherBuild1 = bd.caseOther(n_a, n_b, n_c)
//    val caseOtherBuild2 = bd.caseOther(n_a, n_b, n_c, n_d, n_e)
//    val caseOtherBuild3 = bd.caseOther(n_a, n_b, n_c, n_d, n_e, n_f, n_g)
//
//    assert(caseOtherBuild1 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))
//    assertThrows[IllegalArgumentException](bd.caseOther(n_a, n_b, n_c, n_d))
//    assert(caseOtherBuild2 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e))
//    assertThrows[IllegalArgumentException](bd.caseOther(n_a, n_b, n_c, n_d, n_e, n_f))
//    assert(caseOtherBuild3 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g))
//
//    val iteBuild1 = bd.ite(n_a, n_b, n_c)
//
//    assert(iteBuild1 == OperEx(TlaControlOper.ifThenElse, n_a, n_b, n_c))
//
//    //    val letInBuild1 = bd.letIn( n_a, TlaOperDecl( "b" , List(), n_c ) )
//    //    val letInBuild2 =
//    //      bd.letIn(
//    //        n_a,
//    //        TlaOperDecl(
//    //          "b" ,
//    //          List(
//    //            SimpleFormalParam( "x" ),
//    //            OperFormalParam( "f", FixedArity( 0 ) )
//    //          ),
//    //          n_c
//    //        )
//    //      )
//    //
//    //    assert( letInBuild1 == OperEx( new LetInOper( List(TlaOperDecl( "b" , List(), n_c ) ) ), n_a ) )
//
//  }
//
//  test("Test direct methods: TlaTempOper") {
//    val AABuild = bd.AA(n_a, n_b)
//
//    assert(AABuild == OperEx(TlaTempOper.AA, n_a, n_b))
//
//    val EEBuild = bd.EE(n_a, n_b)
//
//    assert(EEBuild == OperEx(TlaTempOper.EE, n_a, n_b))
//
//    val boxBuild = bd.box(n_a)
//
//    assert(boxBuild == OperEx(TlaTempOper.box, n_a))
//
//    val diamondBuild = bd.diamond(n_a)
//
//    assert(diamondBuild == OperEx(TlaTempOper.diamond, n_a))
//
//    val leadsToBuild = bd.leadsTo(n_a, n_b)
//
//    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, n_a, n_b))
//
//    val guaranteesBuild = bd.guarantees(n_a, n_b)
//
//    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, n_a, n_b))
//
//    val strongFairnessBuild = bd.SF(n_a, n_b)
//
//    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, n_a, n_b))
//
//    val weakFairnessBuild = bd.WF(n_a, n_b)
//
//    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, n_a, n_b))
//  }
//
//  test("Test direct methods: TlaArithOper") {
//    val plusBuild1 = bd.plus(n_a, n_b)
//    val plusBuild2 = bd.plus(n_a, bd.int(2))
//    val plusBuild3 = bd.plus(bd.int(1), n_b)
//    val plusBuild4 = bd.plus(bd.int(1), bd.int(2))
//
//    assert(plusBuild1 == OperEx(TlaArithOper.plus, n_a, n_b))
//    assert(plusBuild2 == OperEx(TlaArithOper.plus, n_a, ValEx(TlaInt(2))))
//    assert(plusBuild3 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), n_b))
//    assert(plusBuild4 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val minusBuild1 = bd.minus(n_a, n_b)
//    val minusBuild2 = bd.minus(n_a, bd.int(2))
//    val minusBuild3 = bd.minus(bd.int(1), n_b)
//    val minusBuild4 = bd.minus(bd.int(1), bd.int(2))
//
//    assert(minusBuild1 == OperEx(TlaArithOper.minus, n_a, n_b))
//    assert(minusBuild2 == OperEx(TlaArithOper.minus, n_a, ValEx(TlaInt(2))))
//    assert(minusBuild3 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), n_b))
//    assert(minusBuild4 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val uminusBuild = bd.uminus(n_a)
//
//    assert(uminusBuild == OperEx(TlaArithOper.uminus, n_a))
//
//    val prodBuild1 = bd.prod()
//    val prodBuild2 = bd.prod(n_a, n_b)
//
//    assert(prodBuild1 == OperEx(TlaArithOper.prod))
//    assert(prodBuild2 == OperEx(TlaArithOper.prod, n_a, n_b))
//
//    val multBuild1 = bd.mult(n_a, n_b)
//    val multBuild2 = bd.mult(n_a, bd.int(2))
//    val multBuild3 = bd.mult(bd.int(1), n_b)
//    val multBuild4 = bd.mult(bd.int(1), bd.int(2))
//
//    assert(multBuild1 == OperEx(TlaArithOper.mult, n_a, n_b))
//    assert(multBuild2 == OperEx(TlaArithOper.mult, n_a, ValEx(TlaInt(2))))
//    assert(multBuild3 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), n_b))
//    assert(multBuild4 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val divBuild1 = bd.div(n_a, n_b)
//    val divBuild2 = bd.div(n_a, bd.int(2))
//    val divBuild3 = bd.div(bd.int(1), n_b)
//    val divBuild4 = bd.div(bd.int(1), bd.int(2))
//
//    assert(divBuild1 == OperEx(TlaArithOper.div, n_a, n_b))
//    assert(divBuild2 == OperEx(TlaArithOper.div, n_a, ValEx(TlaInt(2))))
//    assert(divBuild3 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), n_b))
//    assert(divBuild4 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val modBuild1 = bd.mod(n_a, n_b)
//    val modBuild2 = bd.mod(n_a, bd.int(2))
//    val modBuild3 = bd.mod(bd.int(1), n_b)
//    val modBuild4 = bd.mod(bd.int(1), bd.int(2))
//
//    assert(modBuild1 == OperEx(TlaArithOper.mod, n_a, n_b))
//    assert(modBuild2 == OperEx(TlaArithOper.mod, n_a, ValEx(TlaInt(2))))
//    assert(modBuild3 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), n_b))
//    assert(modBuild4 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    //    val realDivBuild1 = utBd.rDiv(n_a, n_b)
//    //    val realDivBuild2 = utBd.rDiv(n_a, utBd.int(2))
//    //    val realDivBuild3 = utBd.rDiv(utBd.int(1), n_b)
//    //    val realDivBuild4 = utBd.rDiv(utBd.int(1), utBd.int(2))
//    //
//    //    assert(realDivBuild1 == OperEx(TlaArithOper.realDiv, n_a, n_b))
//    //    assert(realDivBuild2 == OperEx(TlaArithOper.realDiv, n_a, ValEx(TlaInt(2))))
//    //    assert(realDivBuild3 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), n_b))
//    //    assert(realDivBuild4 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val expBuild1 = bd.exp(n_a, n_b)
//    val expBuild2 = bd.exp(n_a, bd.int(2))
//    val expBuild3 = bd.exp(bd.int(1), n_b)
//    val expBuild4 = bd.exp(bd.int(1), bd.int(2))
//
//    assert(expBuild1 == OperEx(TlaArithOper.exp, n_a, n_b))
//    assert(expBuild2 == OperEx(TlaArithOper.exp, n_a, ValEx(TlaInt(2))))
//    assert(expBuild3 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), n_b))
//    assert(expBuild4 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val dotdotBuild1 = bd.dotdot(n_a, n_b)
//    val dotdotBuild2 = bd.dotdot(n_a, bd.int(2))
//    val dotdotBuild3 = bd.dotdot(bd.int(1), n_b)
//    val dotdotBuild4 = bd.dotdot(bd.int(1), bd.int(2))
//
//    assert(dotdotBuild1 == OperEx(TlaArithOper.dotdot, n_a, n_b))
//    assert(dotdotBuild2 == OperEx(TlaArithOper.dotdot, n_a, ValEx(TlaInt(2))))
//    assert(dotdotBuild3 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), n_b))
//    assert(dotdotBuild4 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val ltBuild1 = bd.lt(n_a, n_b)
//    val ltBuild2 = bd.lt(n_a, bd.int(2))
//    val ltBuild3 = bd.lt(bd.int(1), n_b)
//    val ltBuild4 = bd.lt(bd.int(1), bd.int(2))
//
//    assert(ltBuild1 == OperEx(TlaArithOper.lt, n_a, n_b))
//    assert(ltBuild2 == OperEx(TlaArithOper.lt, n_a, ValEx(TlaInt(2))))
//    assert(ltBuild3 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), n_b))
//    assert(ltBuild4 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val gtBuild1 = bd.gt(n_a, n_b)
//    val gtBuild2 = bd.gt(n_a, bd.int(2))
//    val gtBuild3 = bd.gt(bd.int(1), n_b)
//    val gtBuild4 = bd.gt(bd.int(1), bd.int(2))
//
//    assert(gtBuild1 == OperEx(TlaArithOper.gt, n_a, n_b))
//    assert(gtBuild2 == OperEx(TlaArithOper.gt, n_a, ValEx(TlaInt(2))))
//    assert(gtBuild3 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), n_b))
//    assert(gtBuild4 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val leBuild1 = bd.le(n_a, n_b)
//    val leBuild2 = bd.le(n_a, bd.int(2))
//    val leBuild3 = bd.le(bd.int(1), n_b)
//    val leBuild4 = bd.le(bd.int(1), bd.int(2))
//
//    assert(leBuild1 == OperEx(TlaArithOper.le, n_a, n_b))
//    assert(leBuild2 == OperEx(TlaArithOper.le, n_a, ValEx(TlaInt(2))))
//    assert(leBuild3 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), n_b))
//    assert(leBuild4 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//
//    val geBuild1 = bd.ge(n_a, n_b)
//    val geBuild2 = bd.ge(n_a, bd.int(2))
//    val geBuild3 = bd.ge(bd.int(1), n_b)
//    val geBuild4 = bd.ge(bd.int(1), bd.int(2))
//
//    assert(geBuild1 == OperEx(TlaArithOper.ge, n_a, n_b))
//    assert(geBuild2 == OperEx(TlaArithOper.ge, n_a, ValEx(TlaInt(2))))
//    assert(geBuild3 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), n_b))
//    assert(geBuild4 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
//  }
//
//  test("Test direct methods: TlaFiniteSetOper") {
//    val cardinalityBuild = bd.card(n_a)
//
//    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, n_a))
//
//    val isFiniteSetBuild = bd.isFin(n_a)
//
//    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, n_a))
//  }
//
//  test("Test direct methods: TlaFunOper") {
//    val appBuild = bd.appFun(n_a, n_b)
//
//    assert(appBuild == OperEx(TlaFunOper.app, n_a, n_b))
//
//    val domainBuild = bd.dom(n_a)
//
//    assert(domainBuild == OperEx(TlaFunOper.domain, n_a))
//
//    val enumBuild1 = bd.enumFun(n_a, n_b)
//    val enumBuild2 = bd.enumFun(n_a, n_b, n_c, n_d)
//
//    assert(enumBuild1 == OperEx(TlaFunOper.enum, n_a, n_b))
//    assertThrows[IllegalArgumentException](bd.enumFun(n_a, n_b, n_c))
//    assert(enumBuild2 == OperEx(TlaFunOper.enum, n_a, n_b, n_c, n_d))
//    assertThrows[IllegalArgumentException](bd.enumFun(n_a, n_b, n_c, n_d, n_e))
//
//    val exceptBuild1 = bd.except(n_a, n_b, n_c)
//    val exceptBuild2 = bd.except(n_a, n_b, n_c, n_d, n_e)
//
//    assert(exceptBuild1 == OperEx(TlaFunOper.except, n_a, n_b, n_c))
//    assertThrows[IllegalArgumentException](bd.except(n_a, n_b, n_c, n_d))
//    assert(exceptBuild2 == OperEx(TlaFunOper.except, n_a, n_b, n_c, n_d, n_e))
//    assertThrows[IllegalArgumentException](bd.except(n_a, n_b, n_c, n_d, n_e, n_f))
//
//    val funDefBuild1 = bd.funDef(n_a, n_b, n_c)
//    val funDefBuild2 = bd.funDef(n_a, n_b, n_c, n_d, n_e)
//
//    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c))
//    assertThrows[IllegalArgumentException](bd.funDef(n_a, n_b, n_c, n_d))
//    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e))
//    assertThrows[IllegalArgumentException](bd.funDef(n_a, n_b, n_c, n_d, n_e, n_f))
//
//    val tupleBuild1 = bd.tuple()
//    val tupleBuild2 = bd.tuple(n_a, n_b)
//
//    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
//    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, n_a, n_b))
//  }
//
//  test("Test direct methods: TlaSeqOper") {
//    val appendBuild = bd.append(n_a, n_b)
//
//    assert(appendBuild == OperEx(TlaSeqOper.append, n_a, n_b))
//
//    val concatBuild = bd.concat(n_a, n_b)
//
//    assert(concatBuild == OperEx(TlaSeqOper.concat, n_a, n_b))
//
//    val headBuild = bd.head(n_a)
//
//    assert(headBuild == OperEx(TlaSeqOper.head, n_a))
//
//    val tailBuild = bd.tail(n_a)
//
//    assert(tailBuild == OperEx(TlaSeqOper.tail, n_a))
//
//    val lenBuild = bd.len(n_a)
//
//    assert(lenBuild == OperEx(TlaSeqOper.len, n_a))
//  }
//
//  test("Test direct methods: TlaSetOper") {
//    val enumSetBuild1 = bd.enumSet()
//    val enumSetBuild2 = bd.enumSet(n_a, n_b)
//
//    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
//    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, n_a, n_b))
//
//    val inBuild = bd.in(n_a, n_b)
//
//    assert(inBuild == OperEx(TlaSetOper.in, n_a, n_b))
//
//    val notinBuild = bd.notin(n_a, n_b)
//
//    assert(notinBuild == OperEx(TlaSetOper.notin, n_a, n_b))
//
//    val capBuild = bd.cap(n_a, n_b)
//
//    assert(capBuild == OperEx(TlaSetOper.cap, n_a, n_b))
//
//    val cupBuild = bd.cup(n_a, n_b)
//
//    assert(cupBuild == OperEx(TlaSetOper.cup, n_a, n_b))
//
//    val unionBuild = bd.union(n_a)
//
//    assert(unionBuild == OperEx(TlaSetOper.union, n_a))
//
//    val filterBuild = bd.filter(n_a, n_b, n_c)
//
//    assert(filterBuild == OperEx(TlaSetOper.filter, n_a, n_b, n_c))
//
//    val mapBuild1 = bd.map(n_a, n_b, n_c)
//    val mapBuild2 = bd.map(n_a, n_b, n_c, n_d, n_e)
//
//    assert(mapBuild1 == OperEx(TlaSetOper.map, n_a, n_b, n_c))
//    assertThrows[IllegalArgumentException](bd.map(n_a, n_b, n_c, n_d))
//    assert(mapBuild2 == OperEx(TlaSetOper.map, n_a, n_b, n_c, n_d, n_e))
//    assertThrows[IllegalArgumentException](bd.map(n_a, n_b, n_c, n_d, n_e, n_f))
//
//    val funSetBuild = bd.funSet(n_a, n_b)
//
//    assert(funSetBuild == OperEx(TlaSetOper.funSet, n_a, n_b))
//
//    val recSetBuild1 = bd.recSet()
//    val recSetBuild2 = bd.recSet(n_a, n_b)
//
//    assert(recSetBuild1 == OperEx(TlaSetOper.recSet))
//    assertThrows[IllegalArgumentException](bd.recSet(n_a))
//    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, n_a, n_b))
//    assertThrows[IllegalArgumentException](bd.recSet(n_a, n_b, n_c))
//
//    val seqSetBuild = bd.seqSet(n_a)
//
//    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, n_a))
//
//    //    val subsetBuild = utBd.subset(n_a, n_b)
//    //
//    //    assert(subsetBuild == OperEx(TlaSetOper.subsetProper, n_a, n_b))
//
//    val subseteqBuild = bd.subseteq(n_a, n_b)
//
//    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, n_a, n_b))
//
//    //    val supsetBuild = utBd.supset(n_a, n_b)
//    //
//    //    assert(supsetBuild == OperEx(TlaSetOper.supsetProper, n_a, n_b))
//
//    //    val supseteqBuild = utBd.supseteq(n_a, n_b)
//    //
//    //    assert(supseteqBuild == OperEx(TlaSetOper.supseteq, n_a, n_b))
//
//    val setminusBuild = bd.setminus(n_a, n_b)
//
//    assert(setminusBuild == OperEx(TlaSetOper.setminus, n_a, n_b))
//
//    val timesBuild1 = bd.times()
//    val timesBuild2 = bd.times(n_a, n_b)
//
//    assert(timesBuild1 == OperEx(TlaSetOper.times))
//    assert(timesBuild2 == OperEx(TlaSetOper.times, n_a, n_b))
//
//    val powSetBuild = bd.powSet(n_a)
//
//    assert(powSetBuild == OperEx(TlaSetOper.powerset, n_a))
//  }

  //  test("Test direct methods: TlcOper") {
  //    val assertMsg = "None"
  //    val assertion = utBd.tlcAssert(NullEx, assertMsg)
  //
  //    assert(assertion == OperEx(TlcOper.assert, NullEx, utBd.str(assertMsg)))
  //  }

}

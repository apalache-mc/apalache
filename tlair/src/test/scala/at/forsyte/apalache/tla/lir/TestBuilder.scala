package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestBuilder extends FunSuite with TestingPredefs {
  private val bd = new Builder()

  test("Test direct methods: Names and values") {
    val nameBuild: TlaEx = bd.name("a")

    assert(nameBuild == NameEx("a"))

    val vBigInt: BigInt = BigInt("1000000015943534656464398536")
    val vBigDecimal: BigDecimal = 1.111132454253626474876842798573504607
    val vBool: Boolean = false
    val vString: String = "a string val"

    val biBuild = bd.bigInt(vBigInt).untyped()
    val bdBuild = bd.decimal(vBigDecimal).untyped()
    val boolBuild = bd.bool(vBool).untyped()
    val strBuild = bd.str(vString).untyped()

    assert(biBuild == ValEx(TlaInt(vBigInt)))
    assert(bdBuild == ValEx(TlaDecimal(vBigDecimal)))
    assert(boolBuild == ValEx(TlaBool(vBool)))
    assert(strBuild == ValEx(TlaStr(vString)))
  }

  test("Test direct methods: Declarations") {
    val decl1 = bd.declOp("A", n_c).untypedOperDecl()
    val decl2 = bd.declOp("A", n_x, "x").untypedOperDecl()
    val decl3 = bd.declOp("A", bd.appOp(n_B), ("B", 0)).untypedOperDecl()
    val decl4 = bd.declOp("A", bd.appOp(n_B, n_x), "x", ("B", 1)).untypedOperDecl()

    assert(decl1 == TlaOperDecl("A", List(), n_c))
    assert(decl2 == TlaOperDecl("A", List(SimpleFormalParam("x")), n_x))
    assert(
        decl3 ==
          TlaOperDecl(
              "A",
              List(OperFormalParam("B", 0)),
              OperEx(TlaOper.apply, n_B)
          ))
    assert(
        decl4 ==
          TlaOperDecl(
              "A",
              List(SimpleFormalParam("x"), OperFormalParam("B", 1)),
              OperEx(TlaOper.apply, n_B, n_x)
          ))

    val appEx1 = bd.appDecl(decl1).untyped()
    val appEx2 = bd.appDecl(decl2, n_a).untyped()
    val appEx3 = bd.appDecl(decl3, n_a).untyped()
    val appEx4 = bd.appDecl(decl4, n_a, n_b).untyped()

    assert(appEx1 == OperEx(TlaOper.apply, name(decl1.name)))
    assertThrows[IllegalArgumentException](bd.appDecl(decl1, n_a))
    assertThrows[IllegalArgumentException](bd.appDecl(decl2))
    assert(appEx2 == OperEx(TlaOper.apply, name(decl2.name), n_a))
    assertThrows[IllegalArgumentException](bd.appDecl(decl2, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.appDecl(decl3))
    assert(appEx3 == OperEx(TlaOper.apply, name(decl3.name), n_a))
    assertThrows[IllegalArgumentException](bd.appDecl(decl3, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4, n_a))
    assert(appEx4 == OperEx(TlaOper.apply, name(decl4.name), n_a, n_b))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4, n_a, n_b, n_c))
  }

  test("Test byName: bad calls") {
    assertThrows[NoSuchElementException](bd.byName("not an operator name", NullEx, n_b))

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, NullEx).untyped())
  }

  test("Test byNameOrNull: bad calls") {
    val nullBadName = bd.byNameOrNull("not an operator name", NullEx, n_b).untyped()

    assert(nullBadName == NullEx)

    val nullBadArity = bd.byNameOrNull(TlaArithOper.plus.name, NullEx).untyped()

    assert(nullBadArity == NullEx)
  }

  test("Test direct methods: TlaOper") {
    val eqBuild1 = bd.eql(n_a, n_b).untyped()
    val eqBuild2 = bd.eql(n_a, bd.int(2)).untyped()

    assert(eqBuild1 == OperEx(TlaOper.eq, n_a, n_b))
    assert(eqBuild2 == OperEx(TlaOper.eq, n_a, ValEx(TlaInt(2))))

    val neBuild1 = bd.neql(n_a, n_b).untyped()
    val neBuild2 = bd.neql(n_a, bd.int(2)).untyped()

    assert(neBuild1 == OperEx(TlaOper.ne, n_a, n_b))
    assert(neBuild2 == OperEx(TlaOper.ne, n_a, ValEx(TlaInt(2))))

    val applyBuild1 = bd.appOp(n_a).untyped()
    val applyBuild2 = bd.appOp(n_a, n_b).untyped()
    val applyBuild3 = bd.appOp(n_a, n_b, n_c).untyped()
    val applyBuild4 = bd.appOp(n_a, n_b, n_c, n_d).untyped()

    assert(applyBuild1 == OperEx(TlaOper.apply, n_a))
    assert(applyBuild2 == OperEx(TlaOper.apply, n_a, n_b))
    assert(applyBuild3 == OperEx(TlaOper.apply, n_a, n_b, n_c))
    assert(applyBuild4 == OperEx(TlaOper.apply, n_a, n_b, n_c, n_d))

    val chooseBuild1 = bd.choose(n_a, n_b).untyped()
    val chooseBuild2 = bd.choose(n_a, n_b, n_c).untyped()

    assert(chooseBuild1 == OperEx(TlaOper.chooseUnbounded, n_a, n_b))
    assert(chooseBuild2 == OperEx(TlaOper.chooseBounded, n_a, n_b, n_c))
  }

  test("Test byName: TlaOper") {
    val eqBuild = bd.byName(TlaOper.eq.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.eq.name, n_a).untyped())
    assert(eqBuild == OperEx(TlaOper.eq, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.eq.name, n_a, n_b, n_c).untyped())

    val neBuild = bd.byName(TlaOper.ne.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.ne.name, n_a).untyped())
    assert(neBuild == OperEx(TlaOper.ne, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.ne.name, n_a, n_b, n_c).untyped())

    val cbBuild = bd.byName(TlaOper.chooseBounded.name, n_a, n_b, n_c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseBounded.name, n_a, n_b).untyped())
    assert(cbBuild == OperEx(TlaOper.chooseBounded, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseBounded.name, n_a, n_b, n_c, n_d).untyped())

    val cubBuild = bd.byName(TlaOper.chooseUnbounded.name, n_a, n_b).untyped()

    assert(cubBuild == OperEx(TlaOper.chooseUnbounded, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseUnbounded.name, n_a, n_b, n_c).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseUnbounded.name, n_a, n_b, n_c, n_d).untyped())
  }

  test("Test byNameOrNull: TlaOper") {
    val eqBuildBad1 = bd.byNameOrNull(TlaOper.eq.name, n_a).untyped()
    val eqBuild = bd.byNameOrNull(TlaOper.eq.name, n_a, n_b).untyped()
    val eqBuildBad2 = bd.byNameOrNull(TlaOper.eq.name, n_a, n_b, n_c).untyped()

    assert(eqBuildBad1 == NullEx)
    assert(eqBuild == OperEx(TlaOper.eq, n_a, n_b))
    assert(eqBuildBad2 == NullEx)

    val neBuildBad1 = bd.byNameOrNull(TlaOper.ne.name, n_a).untyped()
    val neBuild = bd.byNameOrNull(TlaOper.ne.name, n_a, n_b).untyped()
    val neBuildBad2 = bd.byNameOrNull(TlaOper.ne.name, n_a, n_b, n_c).untyped()

    assert(neBuildBad1 == NullEx)
    assert(neBuild == OperEx(TlaOper.ne, n_a, n_b))
    assert(neBuildBad2 == NullEx)

    val cbBuildBad1 = bd.byNameOrNull(TlaOper.chooseBounded.name, n_a, n_b).untyped()
    val cbBuild = bd.byNameOrNull(TlaOper.chooseBounded.name, n_a, n_b, n_c).untyped()
    val cbBuildBad2 = bd.byNameOrNull(TlaOper.chooseBounded.name, n_a, n_b, n_c, n_d).untyped()

    assert(cbBuildBad1 == NullEx)
    assert(cbBuild == OperEx(TlaOper.chooseBounded, n_a, n_b, n_c))
    assert(cbBuildBad2 == NullEx)

    val cubBuild = bd.byNameOrNull(TlaOper.chooseUnbounded.name, n_a, n_b).untyped()
    val cubBuildBad1 = bd.byNameOrNull(TlaOper.chooseUnbounded.name, n_a, n_b, n_c).untyped()
    val cubBuildBad2 = bd.byNameOrNull(TlaOper.chooseUnbounded.name, n_a, n_b, n_c, n_d).untyped()

    assert(cubBuild == OperEx(TlaOper.chooseUnbounded, n_a, n_b))
    assert(cubBuildBad1 == NullEx)
    assert(cubBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaBoolOper ") {
    val andBuild1 = bd.and(n_a).untyped()
    val andBuild2 = bd.and(n_a, n_b).untyped()
    val andBuild3 = bd.and(n_a, n_b, n_c).untyped()
    val andBuild4 = bd.and(n_a, n_b, n_c, n_d).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and, n_a))
    assert(andBuild2 == OperEx(TlaBoolOper.and, n_a, n_b))
    assert(andBuild3 == OperEx(TlaBoolOper.and, n_a, n_b, n_c))
    assert(andBuild4 == OperEx(TlaBoolOper.and, n_a, n_b, n_c, n_d))

    val orBuild1 = bd.or(n_a).untyped()
    val orBuild2 = bd.or(n_a, n_b).untyped()
    val orBuild3 = bd.or(n_a, n_b, n_c).untyped()
    val orBuild4 = bd.or(n_a, n_b, n_c, n_d).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or, n_a))
    assert(orBuild2 == OperEx(TlaBoolOper.or, n_a, n_b))
    assert(orBuild3 == OperEx(TlaBoolOper.or, n_a, n_b, n_c))
    assert(orBuild4 == OperEx(TlaBoolOper.or, n_a, n_b, n_c, n_d))

    val notBuild1 = bd.not(n_a).untyped()

    assert(notBuild1 == OperEx(TlaBoolOper.not, n_a))

    val impliesBuild1 = bd.impl(n_a, n_b).untyped()

    assert(impliesBuild1 == OperEx(TlaBoolOper.implies, n_a, n_b))

    val equivBuild1 = bd.equiv(n_a, n_b).untyped()

    assert(equivBuild1 == OperEx(TlaBoolOper.equiv, n_a, n_b))

    val forallBuild1 = bd.forall(n_a, n_b).untyped()
    val forallBuild2 = bd.forall(n_a, n_b, n_c).untyped()

    assert(forallBuild1 == OperEx(TlaBoolOper.forallUnbounded, n_a, n_b))
    assert(forallBuild2 == OperEx(TlaBoolOper.forall, n_a, n_b, n_c))

    val existsBuild1 = bd.exists(n_a, n_b).untyped()
    val existsBuild2 = bd.exists(n_a, n_b, n_c).untyped()

    assert(existsBuild1 == OperEx(TlaBoolOper.existsUnbounded, n_a, n_b))
    assert(existsBuild2 == OperEx(TlaBoolOper.exists, n_a, n_b, n_c))
  }

  test("Test byName: TlaBoolOper ") {
    val andBuild1 = bd.byName(TlaBoolOper.and.name).untyped()
    val andBuild2 = bd.byName(TlaBoolOper.and.name, n_a).untyped()
    val andBuild3 = bd.byName(TlaBoolOper.and.name, n_a, n_b).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and))
    assert(andBuild2 == OperEx(TlaBoolOper.and, n_a))
    assert(andBuild3 == OperEx(TlaBoolOper.and, n_a, n_b))

    val orBuild1 = bd.byName(TlaBoolOper.or.name).untyped()
    val orBuild2 = bd.byName(TlaBoolOper.or.name, n_a).untyped()
    val orBuild3 = bd.byName(TlaBoolOper.or.name, n_a, n_b).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or))
    assert(orBuild2 == OperEx(TlaBoolOper.or, n_a))
    assert(orBuild3 == OperEx(TlaBoolOper.or, n_a, n_b))

    val notBuild = bd.byName(TlaBoolOper.not.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.not.name).untyped())
    assert(notBuild == OperEx(TlaBoolOper.not, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.not.name, n_a, n_b).untyped())

    val impliesBuild = bd.byName(TlaBoolOper.implies.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.implies.name, n_a).untyped())
    assert(impliesBuild == OperEx(TlaBoolOper.implies, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.implies.name, n_a, n_b, n_c).untyped())

  }

  test("Test byNameOrNull: TlaBoolOper ") {
    val andBuild1 = bd.byNameOrNull(TlaBoolOper.and.name).untyped()
    val andBuild2 = bd.byNameOrNull(TlaBoolOper.and.name, n_a).untyped()
    val andBuild3 = bd.byNameOrNull(TlaBoolOper.and.name, n_a, n_b).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and))
    assert(andBuild2 == OperEx(TlaBoolOper.and, n_a))
    assert(andBuild3 == OperEx(TlaBoolOper.and, n_a, n_b))

    val orBuild1 = bd.byNameOrNull(TlaBoolOper.or.name).untyped()
    val orBuild2 = bd.byNameOrNull(TlaBoolOper.or.name, n_a).untyped()
    val orBuild3 = bd.byNameOrNull(TlaBoolOper.or.name, n_a, n_b).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or))
    assert(orBuild2 == OperEx(TlaBoolOper.or, n_a))
    assert(orBuild3 == OperEx(TlaBoolOper.or, n_a, n_b))

    val notBuildBad1 = bd.byNameOrNull(TlaBoolOper.not.name).untyped()
    val notBuild = bd.byNameOrNull(TlaBoolOper.not.name, n_a).untyped()
    val notBuildBad2 = bd.byNameOrNull(TlaBoolOper.not.name, n_a, n_b).untyped()

    assert(notBuildBad1 == NullEx)
    assert(notBuild == OperEx(TlaBoolOper.not, n_a))
    assert(notBuildBad2 == NullEx)

    val impliesBuildBad1 = bd.byNameOrNull(TlaBoolOper.implies.name, n_a).untyped()
    val impliesBuild = bd.byNameOrNull(TlaBoolOper.implies.name, n_a, n_b).untyped()
    val impliesBuildBad2 = bd.byNameOrNull(TlaBoolOper.implies.name, n_a, n_b, n_c).untyped()

    assert(impliesBuildBad1 == NullEx)
    assert(impliesBuild == OperEx(TlaBoolOper.implies, n_a, n_b))
    assert(impliesBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaActionOper") {
    val primeBuild1 = bd.prime(n_a).untyped()
    val primeBuild2 = bd.prime(bd.name("name")).untyped()

    assert(primeBuild1 == OperEx(TlaActionOper.prime, n_a))
    assert(primeBuild2 == OperEx(TlaActionOper.prime, NameEx("name")))

    val primeEqBuild1 = bd.primeEq(bd.name("name"), n_a).untyped()
    val primeEqBuild2 = bd.primeEq(n_a, n_b).untyped()
    val primeEqBuild3 = bd.primeEq(bd.name("name"), bd.int(1)).untyped()
    val primeEqBuild4 = bd.primeEq(n_a, bd.int(2)).untyped()
    val primeEqBuild5 = bd.primeEq(bd.name("name1"), bd.name("name2")).untyped()

    assert(primeEqBuild1 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name")), n_a))
    assert(primeEqBuild2 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, n_a), n_b))
    assert(primeEqBuild3 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name")), ValEx(TlaInt(1))))
    assert(primeEqBuild4 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, n_a), ValEx(TlaInt(2))))
    assert(primeEqBuild5 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name1")), NameEx("name2")))

    val stutterBuild = bd.stutt(n_a, n_b).untyped()

    assert(stutterBuild == OperEx(TlaActionOper.stutter, n_a, n_b))

    val nostutterBuild = bd.nostutt(n_a, n_b).untyped()

    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, n_a, n_b))

    val enabledBuild = bd.enabled(n_a).untyped()

    assert(enabledBuild == OperEx(TlaActionOper.enabled, n_a))

    val unchangedBuild = bd.unchanged(n_a).untyped()

    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, n_a))

    val compositionBuild = bd.comp(n_a, n_b).untyped()

    assert(compositionBuild == OperEx(TlaActionOper.composition, n_a, n_b))

  }

  test("Test byName: TlaActionOper") {
    val primeBuild = bd.byNameOrNull(TlaActionOper.prime.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.prime.name).untyped())
    assert(primeBuild == OperEx(TlaActionOper.prime, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.prime.name, n_a, n_b).untyped())

    val stutterBuild = bd.byName(TlaActionOper.stutter.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.stutter.name, n_a).untyped())
    assert(stutterBuild == OperEx(TlaActionOper.stutter, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.stutter.name, n_a, n_b, n_c).untyped())

    val nostutterBuild = bd.byName(TlaActionOper.nostutter.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.nostutter.name, n_a).untyped())
    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.nostutter.name, n_a, n_b, n_c).untyped())

    val enabledBuild = bd.byName(TlaActionOper.enabled.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.enabled.name).untyped())
    assert(enabledBuild == OperEx(TlaActionOper.enabled, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.enabled.name, n_a, n_b).untyped())

    val unchangedBuild = bd.byName(TlaActionOper.unchanged.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.unchanged.name).untyped())
    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.unchanged.name, n_a, n_b).untyped())

    val compositionBuild = bd.byName(TlaActionOper.composition.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.composition.name, n_a).untyped())
    assert(compositionBuild == OperEx(TlaActionOper.composition, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.composition.name, n_a, n_b, n_c).untyped())
  }

  test("Test byNameOrNull: TlaActionOper") {
    val primeBuildBad1 = bd.byNameOrNull(TlaActionOper.prime.name).untyped()
    val primeBuild = bd.byNameOrNull(TlaActionOper.prime.name, n_a).untyped()
    val primeBuildBad2 = bd.byNameOrNull(TlaActionOper.prime.name, n_a, n_b).untyped()

    assert(primeBuildBad1 == NullEx)
    assert(primeBuild == OperEx(TlaActionOper.prime, n_a))
    assert(primeBuildBad2 == NullEx)

    val stutterBuildBad1 = bd.byNameOrNull(TlaActionOper.stutter.name, n_a).untyped()
    val stutterBuild = bd.byNameOrNull(TlaActionOper.stutter.name, n_a, n_b).untyped()
    val stutterBuildBad2 = bd.byNameOrNull(TlaActionOper.stutter.name, n_a, n_b, n_c).untyped()

    assert(stutterBuildBad1 == NullEx)
    assert(stutterBuild == OperEx(TlaActionOper.stutter, n_a, n_b))
    assert(stutterBuildBad2 == NullEx)

    val nostutterBuildBad1 = bd.byNameOrNull(TlaActionOper.nostutter.name, n_a).untyped()
    val nostutterBuild = bd.byNameOrNull(TlaActionOper.nostutter.name, n_a, n_b).untyped()
    val nostutterBuildBad2 = bd.byNameOrNull(TlaActionOper.nostutter.name, n_a, n_b, n_c).untyped()

    assert(nostutterBuildBad1 == NullEx)
    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, n_a, n_b))
    assert(nostutterBuildBad2 == NullEx)

    val enabledBuildBad1 = bd.byNameOrNull(TlaActionOper.enabled.name).untyped()
    val enabledBuild = bd.byNameOrNull(TlaActionOper.enabled.name, n_a).untyped()
    val enabledBuildBad2 = bd.byNameOrNull(TlaActionOper.enabled.name, n_a, n_b).untyped()

    assert(enabledBuildBad1 == NullEx)
    assert(enabledBuild == OperEx(TlaActionOper.enabled, n_a))
    assert(enabledBuildBad2 == NullEx)

    val unchangedBuildBad1 = bd.byNameOrNull(TlaActionOper.unchanged.name).untyped()
    val unchangedBuild = bd.byNameOrNull(TlaActionOper.unchanged.name, n_a).untyped()
    val unchangedBuildBad2 = bd.byNameOrNull(TlaActionOper.unchanged.name, n_a, n_b).untyped()

    assert(unchangedBuildBad1 == NullEx)
    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, n_a))
    assert(unchangedBuildBad2 == NullEx)

    val compositionBuildBad1 = bd.byNameOrNull(TlaActionOper.composition.name, n_a).untyped()
    val compositionBuild = bd.byNameOrNull(TlaActionOper.composition.name, n_a, n_b).untyped()
    val compositionBuildBad2 = bd.byNameOrNull(TlaActionOper.composition.name, n_a, n_b, n_c).untyped()

    assert(compositionBuildBad1 == NullEx)
    assert(compositionBuild == OperEx(TlaActionOper.composition, n_a, n_b))
    assert(compositionBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaControlOper") {

    val caseBuild1 = bd.caseAny(n_a, n_b).untyped()
    val caseBuild2 = bd.caseAny(n_a, n_b, n_c).untyped()
    val caseBuild3 = bd.caseAny(n_a, n_b, n_c, n_d).untyped()
    val caseBuild4 = bd.caseAny(n_a, n_b, n_c, n_d, n_e).untyped()
    val caseBuild5 = bd.caseAny(n_a, n_b, n_c, n_d, n_e, n_f).untyped()
    val caseBuild6 = bd.caseAny(n_a, n_b, n_c, n_d, n_e, n_f, n_g).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g))

    val caseSplitBuild1 = bd.caseSplit(n_a, n_b).untyped()
    val caseSplitBuild2 = bd.caseSplit(n_a, n_b, n_c, n_d).untyped()
    val caseSplitBuild3 = bd.caseSplit(n_a, n_b, n_c, n_d, n_e, n_f).untyped()

    assert(caseSplitBuild1 == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.caseSplit(n_a, n_b, n_c).untyped())
    assert(caseSplitBuild2 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d))
    assertThrows[IllegalArgumentException](bd.caseSplit(n_a, n_b, n_c, n_d, n_e).untyped())
    assert(caseSplitBuild3 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f))

    val caseOtherBuild1 = bd.caseOther(n_a, n_b, n_c).untyped()
    val caseOtherBuild2 = bd.caseOther(n_a, n_b, n_c, n_d, n_e).untyped()
    val caseOtherBuild3 = bd.caseOther(n_a, n_b, n_c, n_d, n_e, n_f, n_g).untyped()

    assert(caseOtherBuild1 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.caseOther(n_a, n_b, n_c, n_d).untyped())
    assert(caseOtherBuild2 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e))
    assertThrows[IllegalArgumentException](bd.caseOther(n_a, n_b, n_c, n_d, n_e, n_f).untyped())
    assert(caseOtherBuild3 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g))

    val iteBuild1 = bd.ite(n_a, n_b, n_c).untyped()

    assert(iteBuild1 == OperEx(TlaControlOper.ifThenElse, n_a, n_b, n_c))

    //    val letInBuild1 = bd.letIn( n_a, TlaOperDecl( "b" , List(), n_c ) )
    //    val letInBuild2 =
    //      bd.letIn(
    //        n_a,
    //        TlaOperDecl(
    //          "b" ,
    //          List(
    //            SimpleFormalParam( "x" ),
    //            OperFormalParam( "f", FixedArity( 0 ) )
    //          ),
    //          n_c
    //        )
    //      )
    //
    //    assert( letInBuild1 == OperEx( new LetInOper( List(TlaOperDecl( "b" , List(), n_c ) ) ), n_a ) )

  }

  test("Test byName: TlaControlOper") {
    val caseBuild1 = bd.byName(TlaControlOper.caseNoOther.name, n_a, n_b).untyped()
    val caseBuild2 = bd.byName(TlaControlOper.caseWithOther.name, n_a, n_b, n_c).untyped()
    val caseBuild3 = bd.byName(TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d).untyped()
    val caseBuild4 = bd.byName(TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e).untyped()
    val caseBuild5 = bd.byName(TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d, n_e, n_f).untyped()
    val caseBuild6 = bd.byName(TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e, n_f, n_g).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g))

    val caseNoOtherBuild = bd.byName(TlaControlOper.caseNoOther.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseNoOther.name).untyped())
    assert(caseNoOtherBuild == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseNoOther.name, n_a, n_b, n_c).untyped())

    val caseWithOtherBuild = bd.byName(TlaControlOper.caseWithOther.name, n_a, n_b, n_c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name, n_a).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name, n_a, n_b).untyped())
    assert(caseWithOtherBuild == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))

    val iteBuild = bd.byName(TlaControlOper.ifThenElse.name, n_a, n_b, n_c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.ifThenElse.name, n_a, n_b).untyped())
    assert(iteBuild == OperEx(TlaControlOper.ifThenElse, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.ifThenElse.name, n_a, n_b, n_c, n_d).untyped())
  }

  test("Test byNameOrNull: TlaControlOper") {
    val caseBuild1 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, n_a, n_b).untyped()
    val caseBuild2 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, n_a, n_b, n_c).untyped()
    val caseBuild3 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d).untyped()
    val caseBuild4 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e).untyped()
    val caseBuild5 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d, n_e, n_f).untyped()
    val caseBuild6 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e, n_f, n_g).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g))

    val caseNoOtherBuildEmpty = bd.byNameOrNull(TlaControlOper.caseNoOther.name).untyped()
    val caseNoOtherBuild = bd.byNameOrNull(TlaControlOper.caseNoOther.name, n_a, n_b).untyped()
    val caseNoOtherBuildBad = bd.byNameOrNull(TlaControlOper.caseNoOther.name, n_a, n_b, n_c).untyped()

    assert(caseNoOtherBuildEmpty == NullEx)
    assert(caseNoOtherBuild == OperEx(TlaControlOper.caseNoOther, n_a, n_b))
    assert(caseNoOtherBuildBad == NullEx)

    val caseWithOtherBuildEmpty = bd.byNameOrNull(TlaControlOper.caseWithOther.name).untyped()
    val caseWithOtherBuildSingle = bd.byNameOrNull(TlaControlOper.caseWithOther.name, n_a).untyped()
    val caseWithOtherBuildBad = bd.byNameOrNull(TlaControlOper.caseWithOther.name, n_a, n_b).untyped()
    val caseWithOtherBuild = bd.byNameOrNull(TlaControlOper.caseWithOther.name, n_a, n_b, n_c).untyped()

    assert(caseWithOtherBuildEmpty == NullEx)
    assert(caseWithOtherBuildSingle == NullEx)
    assert(caseWithOtherBuildBad == NullEx)
    assert(caseWithOtherBuild == OperEx(TlaControlOper.caseWithOther, n_a, n_b, n_c))

    val iteBuildBad1 = bd.byNameOrNull(TlaControlOper.ifThenElse.name, n_a, n_b).untyped()
    val iteBuild = bd.byNameOrNull(TlaControlOper.ifThenElse.name, n_a, n_b, n_c).untyped()
    val iteBuildBad2 = bd.byNameOrNull(TlaControlOper.ifThenElse.name, n_a, n_b, n_c, n_d).untyped()

    assert(iteBuildBad1 == NullEx)
    assert(iteBuild == OperEx(TlaControlOper.ifThenElse, n_a, n_b, n_c))
    assert(iteBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaTempOper") {
    val AABuild = bd.AA(n_a, n_b).untyped()

    assert(AABuild == OperEx(TlaTempOper.AA, n_a, n_b))

    val EEBuild = bd.EE(n_a, n_b).untyped()

    assert(EEBuild == OperEx(TlaTempOper.EE, n_a, n_b))

    val boxBuild = bd.box(n_a).untyped()

    assert(boxBuild == OperEx(TlaTempOper.box, n_a))

    val diamondBuild = bd.diamond(n_a).untyped()

    assert(diamondBuild == OperEx(TlaTempOper.diamond, n_a))

    val leadsToBuild = bd.leadsTo(n_a, n_b).untyped()

    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, n_a, n_b))

    val guaranteesBuild = bd.guarantees(n_a, n_b).untyped()

    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, n_a, n_b))

    val strongFairnessBuild = bd.SF(n_a, n_b).untyped()

    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, n_a, n_b))

    val weakFairnessBuild = bd.WF(n_a, n_b).untyped()

    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, n_a, n_b))
  }

  test("Test byName: TlaTempOper") {
    val AABuild = bd.byName(TlaTempOper.AA.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.AA.name, n_a).untyped())
    assert(AABuild == OperEx(TlaTempOper.AA, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.AA.name, n_a, n_b, n_c).untyped())

    val EEBuild = bd.byName(TlaTempOper.EE.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.EE.name, n_a).untyped())
    assert(EEBuild == OperEx(TlaTempOper.EE, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.EE.name, n_a, n_b, n_c).untyped())

    val boxBuild = bd.byName(TlaTempOper.box.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.box.name).untyped())
    assert(boxBuild == OperEx(TlaTempOper.box, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.box.name, n_a, n_b).untyped())

    val diamondBuild = bd.byName(TlaTempOper.diamond.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.diamond.name).untyped())
    assert(diamondBuild == OperEx(TlaTempOper.diamond, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.diamond.name, n_a, n_b).untyped())

    val leadsToBuild = bd.byName(TlaTempOper.leadsTo.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.leadsTo.name, n_a).untyped())
    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.leadsTo.name, n_a, n_b, n_c).untyped())

    val guaranteesBuild = bd.byName(TlaTempOper.guarantees.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.guarantees.name, n_a).untyped())
    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.guarantees.name, n_a, n_b, n_c).untyped())

    val strongFairnessBuild = bd.byName(TlaTempOper.strongFairness.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.strongFairness.name, n_a).untyped())
    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.strongFairness.name, n_a, n_b, n_c).untyped())

    val weakFairnessBuild = bd.byName(TlaTempOper.weakFairness.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.weakFairness.name, n_a).untyped())
    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.weakFairness.name, n_a, n_b, n_c).untyped())

  }

  test("Test byNameOrNull: TlaTempOper") {
    val AABuildBad1 = bd.byNameOrNull(TlaTempOper.AA.name, n_a).untyped()
    val AABuild = bd.byNameOrNull(TlaTempOper.AA.name, n_a, n_b).untyped()
    val AABuildBad2 = bd.byNameOrNull(TlaTempOper.AA.name, n_a, n_b, n_c).untyped()

    assert(AABuildBad1 == NullEx)
    assert(AABuild == OperEx(TlaTempOper.AA, n_a, n_b))
    assert(AABuildBad2 == NullEx)

    val EEBuildBad1 = bd.byNameOrNull(TlaTempOper.EE.name, n_a).untyped()
    val EEBuild = bd.byNameOrNull(TlaTempOper.EE.name, n_a, n_b).untyped()
    val EEBuildBad2 = bd.byNameOrNull(TlaTempOper.EE.name, n_a, n_b, n_c).untyped()

    assert(EEBuildBad1 == NullEx)
    assert(EEBuild == OperEx(TlaTempOper.EE, n_a, n_b))
    assert(EEBuildBad2 == NullEx)

    val boxBuildBad1 = bd.byNameOrNull(TlaTempOper.box.name).untyped()
    val boxBuild = bd.byNameOrNull(TlaTempOper.box.name, n_a).untyped()
    val boxBuildBad2 = bd.byNameOrNull(TlaTempOper.box.name, n_a, n_b).untyped()

    assert(boxBuildBad1 == NullEx)
    assert(boxBuild == OperEx(TlaTempOper.box, n_a))
    assert(boxBuildBad2 == NullEx)

    val diamondBuildBad1 = bd.byNameOrNull(TlaTempOper.diamond.name).untyped()
    val diamondBuild = bd.byNameOrNull(TlaTempOper.diamond.name, n_a).untyped()
    val diamondBuildBad2 = bd.byNameOrNull(TlaTempOper.diamond.name, n_a, n_b).untyped()

    assert(diamondBuildBad1 == NullEx)
    assert(diamondBuild == OperEx(TlaTempOper.diamond, n_a))
    assert(diamondBuildBad2 == NullEx)

    val leadsToBuildBad1 = bd.byNameOrNull(TlaTempOper.leadsTo.name, n_a).untyped()
    val leadsToBuild = bd.byNameOrNull(TlaTempOper.leadsTo.name, n_a, n_b).untyped()
    val leadsToBuildBad2 = bd.byNameOrNull(TlaTempOper.leadsTo.name, n_a, n_b, n_c).untyped()

    assert(leadsToBuildBad1 == NullEx)
    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, n_a, n_b))
    assert(leadsToBuildBad2 == NullEx)

    val guaranteesBuildBad1 = bd.byNameOrNull(TlaTempOper.guarantees.name, n_a).untyped()
    val guaranteesBuild = bd.byNameOrNull(TlaTempOper.guarantees.name, n_a, n_b).untyped()
    val guaranteesBuildBad2 = bd.byNameOrNull(TlaTempOper.guarantees.name, n_a, n_b, n_c).untyped()

    assert(guaranteesBuildBad1 == NullEx)
    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, n_a, n_b))
    assert(guaranteesBuildBad2 == NullEx)

    val strongFairnessBuildBad1 = bd.byNameOrNull(TlaTempOper.strongFairness.name, n_a).untyped()
    val strongFairnessBuild = bd.byNameOrNull(TlaTempOper.strongFairness.name, n_a, n_b).untyped()
    val strongFairnessBuildBad2 = bd.byNameOrNull(TlaTempOper.strongFairness.name, n_a, n_b, n_c).untyped()

    assert(strongFairnessBuildBad1 == NullEx)
    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, n_a, n_b))
    assert(strongFairnessBuildBad2 == NullEx)

    val weakFairnessBuildBad1 = bd.byNameOrNull(TlaTempOper.weakFairness.name, n_a).untyped()
    val weakFairnessBuild = bd.byNameOrNull(TlaTempOper.weakFairness.name, n_a, n_b).untyped()
    val weakFairnessBuildBad2 = bd.byNameOrNull(TlaTempOper.weakFairness.name, n_a, n_b, n_c).untyped()

    assert(weakFairnessBuildBad1 == NullEx)
    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, n_a, n_b))
    assert(weakFairnessBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaArithOper") {

    val plusBuild1 = bd.plus(n_a, n_b).untyped()
    val plusBuild2 = bd.plus(n_a, bd.int(2)).untyped()
    val plusBuild3 = bd.plus(bd.int(1), n_b).untyped()
    val plusBuild4 = bd.plus(bd.int(1), bd.int(2)).untyped()

    assert(plusBuild1 == OperEx(TlaArithOper.plus, n_a, n_b))
    assert(plusBuild2 == OperEx(TlaArithOper.plus, n_a, ValEx(TlaInt(2))))
    assert(plusBuild3 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), n_b))
    assert(plusBuild4 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val minusBuild1 = bd.minus(n_a, n_b).untyped()
    val minusBuild2 = bd.minus(n_a, bd.int(2)).untyped()
    val minusBuild3 = bd.minus(bd.int(1), n_b).untyped()
    val minusBuild4 = bd.minus(bd.int(1), bd.int(2)).untyped()

    assert(minusBuild1 == OperEx(TlaArithOper.minus, n_a, n_b))
    assert(minusBuild2 == OperEx(TlaArithOper.minus, n_a, ValEx(TlaInt(2))))
    assert(minusBuild3 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), n_b))
    assert(minusBuild4 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val uminusBuild = bd.uminus(n_a).untyped()

    assert(uminusBuild == OperEx(TlaArithOper.uminus, n_a))

    val multBuild1 = bd.mult(n_a, n_b).untyped()
    val multBuild2 = bd.mult(n_a, bd.int(2)).untyped()
    val multBuild3 = bd.mult(bd.int(1), n_b).untyped()
    val multBuild4 = bd.mult(bd.int(1), bd.int(2)).untyped()

    assert(multBuild1 == OperEx(TlaArithOper.mult, n_a, n_b))
    assert(multBuild2 == OperEx(TlaArithOper.mult, n_a, ValEx(TlaInt(2))))
    assert(multBuild3 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), n_b))
    assert(multBuild4 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val divBuild1 = bd.div(n_a, n_b).untyped()
    val divBuild2 = bd.div(n_a, bd.int(2)).untyped()
    val divBuild3 = bd.div(bd.int(1), n_b).untyped()
    val divBuild4 = bd.div(bd.int(1), bd.int(2)).untyped()

    assert(divBuild1 == OperEx(TlaArithOper.div, n_a, n_b))
    assert(divBuild2 == OperEx(TlaArithOper.div, n_a, ValEx(TlaInt(2))))
    assert(divBuild3 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), n_b))
    assert(divBuild4 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val modBuild1 = bd.mod(n_a, n_b).untyped()
    val modBuild2 = bd.mod(n_a, bd.int(2)).untyped()
    val modBuild3 = bd.mod(bd.int(1), n_b).untyped()
    val modBuild4 = bd.mod(bd.int(1), bd.int(2)).untyped()

    assert(modBuild1 == OperEx(TlaArithOper.mod, n_a, n_b))
    assert(modBuild2 == OperEx(TlaArithOper.mod, n_a, ValEx(TlaInt(2))))
    assert(modBuild3 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), n_b))
    assert(modBuild4 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val realDivBuild1 = bd.rDiv(n_a, n_b).untyped()
    val realDivBuild2 = bd.rDiv(n_a, bd.int(2)).untyped()
    val realDivBuild3 = bd.rDiv(bd.int(1), n_b).untyped()
    val realDivBuild4 = bd.rDiv(bd.int(1), bd.int(2)).untyped()

    assert(realDivBuild1 == OperEx(TlaArithOper.realDiv, n_a, n_b))
    assert(realDivBuild2 == OperEx(TlaArithOper.realDiv, n_a, ValEx(TlaInt(2))))
    assert(realDivBuild3 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), n_b))
    assert(realDivBuild4 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val expBuild1 = bd.exp(n_a, n_b).untyped()
    val expBuild2 = bd.exp(n_a, bd.int(2)).untyped()
    val expBuild3 = bd.exp(bd.int(1), n_b).untyped()
    val expBuild4 = bd.exp(bd.int(1), bd.int(2)).untyped()

    assert(expBuild1 == OperEx(TlaArithOper.exp, n_a, n_b))
    assert(expBuild2 == OperEx(TlaArithOper.exp, n_a, ValEx(TlaInt(2))))
    assert(expBuild3 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), n_b))
    assert(expBuild4 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val dotdotBuild1 = bd.dotdot(n_a, n_b).untyped()
    val dotdotBuild2 = bd.dotdot(n_a, bd.int(2)).untyped()
    val dotdotBuild3 = bd.dotdot(bd.int(1), n_b).untyped()
    val dotdotBuild4 = bd.dotdot(bd.int(1), bd.int(2)).untyped()

    assert(dotdotBuild1 == OperEx(TlaArithOper.dotdot, n_a, n_b))
    assert(dotdotBuild2 == OperEx(TlaArithOper.dotdot, n_a, ValEx(TlaInt(2))))
    assert(dotdotBuild3 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), n_b))
    assert(dotdotBuild4 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val ltBuild1 = bd.lt(n_a, n_b).untyped()
    val ltBuild2 = bd.lt(n_a, bd.int(2)).untyped()
    val ltBuild3 = bd.lt(bd.int(1), n_b).untyped()
    val ltBuild4 = bd.lt(bd.int(1), bd.int(2)).untyped()

    assert(ltBuild1 == OperEx(TlaArithOper.lt, n_a, n_b))
    assert(ltBuild2 == OperEx(TlaArithOper.lt, n_a, ValEx(TlaInt(2))))
    assert(ltBuild3 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), n_b))
    assert(ltBuild4 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val gtBuild1 = bd.gt(n_a, n_b).untyped()
    val gtBuild2 = bd.gt(n_a, bd.int(2)).untyped()
    val gtBuild3 = bd.gt(bd.int(1), n_b).untyped()
    val gtBuild4 = bd.gt(bd.int(1), bd.int(2)).untyped()

    assert(gtBuild1 == OperEx(TlaArithOper.gt, n_a, n_b))
    assert(gtBuild2 == OperEx(TlaArithOper.gt, n_a, ValEx(TlaInt(2))))
    assert(gtBuild3 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), n_b))
    assert(gtBuild4 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val leBuild1 = bd.le(n_a, n_b).untyped()
    val leBuild2 = bd.le(n_a, bd.int(2)).untyped()
    val leBuild3 = bd.le(bd.int(1), n_b).untyped()
    val leBuild4 = bd.le(bd.int(1), bd.int(2)).untyped()

    assert(leBuild1 == OperEx(TlaArithOper.le, n_a, n_b))
    assert(leBuild2 == OperEx(TlaArithOper.le, n_a, ValEx(TlaInt(2))))
    assert(leBuild3 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), n_b))
    assert(leBuild4 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val geBuild1 = bd.ge(n_a, n_b).untyped()
    val geBuild2 = bd.ge(n_a, bd.int(2)).untyped()
    val geBuild3 = bd.ge(bd.int(1), n_b).untyped()
    val geBuild4 = bd.ge(bd.int(1), bd.int(2)).untyped()

    assert(geBuild1 == OperEx(TlaArithOper.ge, n_a, n_b))
    assert(geBuild2 == OperEx(TlaArithOper.ge, n_a, ValEx(TlaInt(2))))
    assert(geBuild3 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), n_b))
    assert(geBuild4 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
  }

  test("Test byName: TlaArithOper") {

    val plusBuild = bd.byName(TlaArithOper.plus.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, n_a).untyped())
    assert(plusBuild == OperEx(TlaArithOper.plus, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, n_a, n_b, n_c).untyped())

    val minusBuild = bd.byName(TlaArithOper.minus.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.minus.name, n_a).untyped())
    assert(minusBuild == OperEx(TlaArithOper.minus, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.minus.name, n_a, n_b, n_c).untyped())

    val uminusBuild = bd.byName(TlaArithOper.uminus.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.uminus.name).untyped())
    assert(uminusBuild == OperEx(TlaArithOper.uminus, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.uminus.name, n_a, n_b, n_c).untyped())

    val multBuild = bd.byName(TlaArithOper.mult.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mult.name, n_a).untyped())
    assert(multBuild == OperEx(TlaArithOper.mult, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mult.name, n_a, n_b, n_c).untyped())

    val divBuild = bd.byName(TlaArithOper.div.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.div.name, n_a).untyped())
    assert(divBuild == OperEx(TlaArithOper.div, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.div.name, n_a, n_b, n_c).untyped())

    val modBuild = bd.byName(TlaArithOper.mod.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mod.name, n_a).untyped())
    assert(modBuild == OperEx(TlaArithOper.mod, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mod.name, n_a, n_b, n_c).untyped())

    val realDivBuild = bd.byName(TlaArithOper.realDiv.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.realDiv.name, n_a).untyped())
    assert(realDivBuild == OperEx(TlaArithOper.realDiv, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.realDiv.name, n_a, n_b, n_c).untyped())

    val expBuild = bd.byName(TlaArithOper.exp.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.exp.name, n_a).untyped())
    assert(expBuild == OperEx(TlaArithOper.exp, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.exp.name, n_a, n_b, n_c).untyped())

    val dotdotBuild = bd.byName(TlaArithOper.dotdot.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.dotdot.name, n_a).untyped())
    assert(dotdotBuild == OperEx(TlaArithOper.dotdot, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.dotdot.name, n_a, n_b, n_c).untyped())

    val ltBuild = bd.byName(TlaArithOper.lt.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.lt.name, n_a).untyped())
    assert(ltBuild == OperEx(TlaArithOper.lt, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.lt.name, n_a, n_b, n_c).untyped())

    val gtBuild = bd.byName(TlaArithOper.gt.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.gt.name, n_a).untyped())
    assert(gtBuild == OperEx(TlaArithOper.gt, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.gt.name, n_a, n_b, n_c).untyped())

    val leBuild = bd.byName(TlaArithOper.le.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.le.name, n_a).untyped())
    assert(leBuild == OperEx(TlaArithOper.le, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.le.name, n_a, n_b, n_c).untyped())

    val geBuild = bd.byName(TlaArithOper.ge.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.ge.name, n_a).untyped())
    assert(geBuild == OperEx(TlaArithOper.ge, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.ge.name, n_a, n_b, n_c).untyped())
  }

  test("Test byNameOrNull: TlaArithOper") {

    val plusBuildBad1 = bd.byNameOrNull(TlaArithOper.plus.name, n_a).untyped()
    val plusBuild = bd.byNameOrNull(TlaArithOper.plus.name, n_a, n_b).untyped()
    val plusBuildBad2 = bd.byNameOrNull(TlaArithOper.plus.name, n_a, n_b, n_c).untyped()

    assert(plusBuildBad1 == NullEx)
    assert(plusBuild == OperEx(TlaArithOper.plus, n_a, n_b))
    assert(plusBuildBad2 == NullEx)

    val minusBuildBad1 = bd.byNameOrNull(TlaArithOper.minus.name, n_a).untyped()
    val minusBuild = bd.byNameOrNull(TlaArithOper.minus.name, n_a, n_b).untyped()
    val minusBuildBad2 = bd.byNameOrNull(TlaArithOper.minus.name, n_a, n_b, n_c).untyped()

    assert(minusBuildBad1 == NullEx)
    assert(minusBuild == OperEx(TlaArithOper.minus, n_a, n_b))
    assert(minusBuildBad2 == NullEx)

    val uminusBuildBad1 = bd.byNameOrNull(TlaArithOper.uminus.name).untyped()
    val uminusBuild = bd.byNameOrNull(TlaArithOper.uminus.name, n_a).untyped()
    val uminusBuildBad2 = bd.byNameOrNull(TlaArithOper.uminus.name, n_a, n_b, n_c).untyped()

    assert(uminusBuildBad1 == NullEx)
    assert(uminusBuild == OperEx(TlaArithOper.uminus, n_a))
    assert(uminusBuildBad2 == NullEx)

    val multBuildBad1 = bd.byNameOrNull(TlaArithOper.mult.name, n_a).untyped()
    val multBuild = bd.byNameOrNull(TlaArithOper.mult.name, n_a, n_b).untyped()
    val multBuildBad2 = bd.byNameOrNull(TlaArithOper.mult.name, n_a, n_b, n_c).untyped()

    assert(multBuildBad1 == NullEx)
    assert(multBuild == OperEx(TlaArithOper.mult, n_a, n_b))
    assert(multBuildBad2 == NullEx)

    val divBuildBad1 = bd.byNameOrNull(TlaArithOper.div.name, n_a).untyped()
    val divBuild = bd.byNameOrNull(TlaArithOper.div.name, n_a, n_b).untyped()
    val divBuildBad2 = bd.byNameOrNull(TlaArithOper.div.name, n_a, n_b, n_c).untyped()

    assert(divBuildBad1 == NullEx)
    assert(divBuild == OperEx(TlaArithOper.div, n_a, n_b))
    assert(divBuildBad2 == NullEx)

    val modBuildBad1 = bd.byNameOrNull(TlaArithOper.mod.name, n_a).untyped()
    val modBuild = bd.byNameOrNull(TlaArithOper.mod.name, n_a, n_b).untyped()
    val modBuildBad2 = bd.byNameOrNull(TlaArithOper.mod.name, n_a, n_b, n_c).untyped()

    assert(modBuildBad1 == NullEx)
    assert(modBuild == OperEx(TlaArithOper.mod, n_a, n_b))
    assert(modBuildBad2 == NullEx)

    val realDivBuildBad1 = bd.byNameOrNull(TlaArithOper.realDiv.name, n_a).untyped()
    val realDivBuild = bd.byNameOrNull(TlaArithOper.realDiv.name, n_a, n_b).untyped()
    val realDivBuildBad2 = bd.byNameOrNull(TlaArithOper.realDiv.name, n_a, n_b, n_c).untyped()

    assert(realDivBuildBad1 == NullEx)
    assert(realDivBuild == OperEx(TlaArithOper.realDiv, n_a, n_b))
    assert(realDivBuildBad2 == NullEx)

    val expBuildBad1 = bd.byNameOrNull(TlaArithOper.exp.name, n_a).untyped()
    val expBuild = bd.byNameOrNull(TlaArithOper.exp.name, n_a, n_b).untyped()
    val expBuildBad2 = bd.byNameOrNull(TlaArithOper.exp.name, n_a, n_b, n_c).untyped()

    assert(expBuildBad1 == NullEx)
    assert(expBuild == OperEx(TlaArithOper.exp, n_a, n_b))
    assert(expBuildBad2 == NullEx)

    val dotdotBuildBad1 = bd.byNameOrNull(TlaArithOper.dotdot.name, n_a).untyped()
    val dotdotBuild = bd.byNameOrNull(TlaArithOper.dotdot.name, n_a, n_b).untyped()
    val dotdotBuildBad2 = bd.byNameOrNull(TlaArithOper.dotdot.name, n_a, n_b, n_c).untyped()

    assert(dotdotBuildBad1 == NullEx)
    assert(dotdotBuild == OperEx(TlaArithOper.dotdot, n_a, n_b))
    assert(dotdotBuildBad2 == NullEx)

    val ltBuildBad1 = bd.byNameOrNull(TlaArithOper.lt.name, n_a).untyped()
    val ltBuild = bd.byNameOrNull(TlaArithOper.lt.name, n_a, n_b).untyped()
    val ltBuildBad2 = bd.byNameOrNull(TlaArithOper.lt.name, n_a, n_b, n_c).untyped()

    assert(ltBuildBad1 == NullEx)
    assert(ltBuild == OperEx(TlaArithOper.lt, n_a, n_b))
    assert(ltBuildBad2 == NullEx)

    val gtBuildBad1 = bd.byNameOrNull(TlaArithOper.gt.name, n_a).untyped()
    val gtBuild = bd.byNameOrNull(TlaArithOper.gt.name, n_a, n_b).untyped()
    val gtBuildBad2 = bd.byNameOrNull(TlaArithOper.gt.name, n_a, n_b, n_c).untyped()

    assert(gtBuildBad1 == NullEx)
    assert(gtBuild == OperEx(TlaArithOper.gt, n_a, n_b))
    assert(gtBuildBad2 == NullEx)

    val leBuildBad1 = bd.byNameOrNull(TlaArithOper.le.name, n_a).untyped()
    val leBuild = bd.byNameOrNull(TlaArithOper.le.name, n_a, n_b).untyped()
    val leBuildBad2 = bd.byNameOrNull(TlaArithOper.le.name, n_a, n_b, n_c).untyped()

    assert(leBuildBad1 == NullEx)
    assert(leBuild == OperEx(TlaArithOper.le, n_a, n_b))
    assert(leBuildBad2 == NullEx)

    val geBuildBad1 = bd.byNameOrNull(TlaArithOper.ge.name, n_a).untyped()
    val geBuild = bd.byNameOrNull(TlaArithOper.ge.name, n_a, n_b).untyped()
    val geBuildBad2 = bd.byNameOrNull(TlaArithOper.ge.name, n_a, n_b, n_c).untyped()

    assert(geBuildBad1 == NullEx)
    assert(geBuild == OperEx(TlaArithOper.ge, n_a, n_b))
    assert(geBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaFiniteSetOper") {
    val cardinalityBuild = bd.card(n_a).untyped()

    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, n_a))

    val isFiniteSetBuild = bd.isFin(n_a).untyped()

    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, n_a))
  }

  test("Test byName: TlaFiniteSetOper") {
    val cardinalityBuild = bd.byName(TlaFiniteSetOper.cardinality.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.cardinality.name).untyped())
    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.cardinality.name, n_a, n_b, n_c).untyped())

    val isFiniteSetBuild = bd.byName(TlaFiniteSetOper.isFiniteSet.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.isFiniteSet.name).untyped())
    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.isFiniteSet.name, n_a, n_b, n_c).untyped())
  }

  test("Test byNameOrNull: TlaFiniteSetOper") {
    val cardinalityBuildBad1 = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name).untyped()
    val cardinalityBuild = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name, n_a).untyped()
    val cardinalityBuildBad2 = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name, n_a, n_b, n_c).untyped()

    assert(cardinalityBuildBad1 == NullEx)
    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, n_a))
    assert(cardinalityBuildBad2 == NullEx)

    val isFiniteSetBuildBad1 = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name).untyped()
    val isFiniteSetBuild = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name, n_a).untyped()
    val isFiniteSetBuildBad2 = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name, n_a, n_b, n_c).untyped()

    assert(isFiniteSetBuildBad1 == NullEx)
    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, n_a))
    assert(isFiniteSetBuildBad2 == NullEx)

  }

  test("Test direct methods: TlaFunOper") {
    val appBuild = bd.appFun(n_a, n_b).untyped()

    assert(appBuild == OperEx(TlaFunOper.app, n_a, n_b))

    val domainBuild = bd.dom(n_a).untyped()

    assert(domainBuild == OperEx(TlaFunOper.domain, n_a))

    val enumBuild1 = bd.enumFun(n_a, n_b).untyped()
    val enumBuild2 = bd.enumFun(n_a, n_b, n_c, n_d).untyped()

    assert(enumBuild1 == OperEx(TlaFunOper.enum, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.enumFun(n_a, n_b, n_c).untyped())
    assert(enumBuild2 == OperEx(TlaFunOper.enum, n_a, n_b, n_c, n_d))
    assertThrows[IllegalArgumentException](bd.enumFun(n_a, n_b, n_c, n_d, n_e).untyped())

    val exceptBuild1 = bd.except(n_a, n_b, n_c).untyped()
    val exceptBuild2 = bd.except(n_a, n_b, n_c, n_d, n_e).untyped()

    assert(exceptBuild1 == OperEx(TlaFunOper.except, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.except(n_a, n_b, n_c, n_d).untyped())
    assert(exceptBuild2 == OperEx(TlaFunOper.except, n_a, n_b, n_c, n_d, n_e))
    assertThrows[IllegalArgumentException](bd.except(n_a, n_b, n_c, n_d, n_e, n_f).untyped())

    val funDefBuild1 = bd.funDef(n_a, n_b, n_c).untyped()
    val funDefBuild2 = bd.funDef(n_a, n_b, n_c, n_d, n_e).untyped()

    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.funDef(n_a, n_b, n_c, n_d).untyped())
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e))
    assertThrows[IllegalArgumentException](bd.funDef(n_a, n_b, n_c, n_d, n_e, n_f).untyped())

    val tupleBuild1 = bd.tuple().untyped()
    val tupleBuild2 = bd.tuple(n_a, n_b).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, n_a, n_b))
  }

  test("Test byName: TlaFunOper") {
    val appBuild = bd.byName(TlaFunOper.app.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.app.name, n_a).untyped())
    assert(appBuild == OperEx(TlaFunOper.app, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.app.name, n_a, n_b, n_c).untyped())

    val domainBuild = bd.byName(TlaFunOper.domain.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.domain.name).untyped())
    assert(domainBuild == OperEx(TlaFunOper.domain, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.domain.name, n_a, n_b, n_c).untyped())

    val enumBuild1 = bd.byName(TlaFunOper.enum.name, n_a, n_b).untyped()
    val enumBuild2 = bd.byName(TlaFunOper.enum.name, n_a, n_b, n_c, n_d).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.enum.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.enum.name, n_a).untyped())
    assert(enumBuild1 == OperEx(TlaFunOper.enum, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.enum.name, n_a, n_b, n_c).untyped())
    assert(enumBuild2 == OperEx(TlaFunOper.enum, n_a, n_b, n_c, n_d))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.enum.name, n_a, n_b, n_c, n_d, n_e).untyped())

    val exceptBuild1 = bd.byName(TlaFunOper.except.name, n_a, n_b, n_c).untyped()
    val exceptBuild2 = bd.byName(TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, n_a).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, n_a, n_b).untyped())
    assert(exceptBuild1 == OperEx(TlaFunOper.except, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, n_a, n_b, n_c, n_d).untyped())
    assert(exceptBuild2 == OperEx(TlaFunOper.except, n_a, n_b, n_c, n_d, n_e))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e, n_f).untyped())

    val funDefBuild1 = bd.byName(TlaFunOper.funDef.name, n_a, n_b, n_c).untyped()
    val funDefBuild2 = bd.byName(TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, n_a).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, n_a, n_b).untyped())
    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, n_a, n_b, n_c, n_d).untyped())
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e, n_f).untyped())

    val tupleBuild1 = bd.byName(TlaFunOper.tuple.name).untyped()
    val tupleBuild2 = bd.byName(TlaFunOper.tuple.name, n_a, n_b).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, n_a, n_b))

  }

  test("Test byNameOrNull: TlaFunOper") {
    val appBuildBad1 = bd.byNameOrNull(TlaFunOper.app.name, n_a).untyped()
    val appBuild = bd.byNameOrNull(TlaFunOper.app.name, n_a, n_b).untyped()
    val appBuildBad2 = bd.byNameOrNull(TlaFunOper.app.name, n_a, n_b, n_c).untyped()

    assert(appBuildBad1 == NullEx)
    assert(appBuild == OperEx(TlaFunOper.app, n_a, n_b))
    assert(appBuildBad2 == NullEx)

    val domainBuildBad1 = bd.byNameOrNull(TlaFunOper.domain.name).untyped()
    val domainBuild = bd.byNameOrNull(TlaFunOper.domain.name, n_a).untyped()
    val domainBuildBad2 = bd.byNameOrNull(TlaFunOper.domain.name, n_a, n_b, n_c).untyped()

    assert(domainBuildBad1 == NullEx)
    assert(domainBuild == OperEx(TlaFunOper.domain, n_a))
    assert(domainBuildBad2 == NullEx)

    val enumBuildEmpty = bd.byNameOrNull(TlaFunOper.enum.name).untyped()
    val enumBuild1 = bd.byNameOrNull(TlaFunOper.enum.name, n_a, n_b).untyped()
    val enumBuildBad1 = bd.byNameOrNull(TlaFunOper.enum.name, n_a, n_b, n_c).untyped()
    val enumBuild2 = bd.byNameOrNull(TlaFunOper.enum.name, n_a, n_b, n_c, n_d).untyped()
    val enumBuildBad2 = bd.byNameOrNull(TlaFunOper.enum.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assert(enumBuildEmpty == NullEx)
    assert(enumBuild1 == OperEx(TlaFunOper.enum, n_a, n_b))
    assert(enumBuildBad1 == NullEx)
    assert(enumBuild2 == OperEx(TlaFunOper.enum, n_a, n_b, n_c, n_d))
    assert(enumBuildBad2 == NullEx)

    val exceptBuildEmpty = bd.byNameOrNull(TlaFunOper.except.name).untyped()
    val exceptBuildSingle = bd.byNameOrNull(TlaFunOper.except.name, n_a).untyped()
    val exceptBuildBad1 = bd.byNameOrNull(TlaFunOper.except.name, n_a, n_b).untyped()
    val exceptBuild1 = bd.byNameOrNull(TlaFunOper.except.name, n_a, n_b, n_c).untyped()
    val exceptBuildBad2 = bd.byNameOrNull(TlaFunOper.except.name, n_a, n_b, n_c, n_d).untyped()
    val exceptBuild2 = bd.byNameOrNull(TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assert(exceptBuildEmpty == NullEx)
    assert(exceptBuildSingle == NullEx)
    assert(exceptBuildBad1 == NullEx)
    assert(exceptBuild1 == OperEx(TlaFunOper.except, n_a, n_b, n_c))
    assert(exceptBuildBad2 == NullEx)
    assert(exceptBuild2 == OperEx(TlaFunOper.except, n_a, n_b, n_c, n_d, n_e))

    val funDefBuildEmpty = bd.byNameOrNull(TlaFunOper.funDef.name).untyped()
    val funDefBuildSingle = bd.byNameOrNull(TlaFunOper.funDef.name, n_a).untyped()
    val funDefBuildBad1 = bd.byNameOrNull(TlaFunOper.funDef.name, n_a, n_b).untyped()
    val funDefBuild1 = bd.byNameOrNull(TlaFunOper.funDef.name, n_a, n_b, n_c).untyped()
    val funDefBuildBad2 = bd.byNameOrNull(TlaFunOper.funDef.name, n_a, n_b, n_c, n_d).untyped()
    val funDefBuild2 = bd.byNameOrNull(TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assert(funDefBuildEmpty == NullEx)
    assert(funDefBuildSingle == NullEx)
    assert(funDefBuildBad1 == NullEx)
    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c))
    assert(funDefBuildBad2 == NullEx)
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e))

    val tupleBuild1 = bd.byNameOrNull(TlaFunOper.tuple.name).untyped()
    val tupleBuild2 = bd.byNameOrNull(TlaFunOper.tuple.name, n_a, n_b).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, n_a, n_b))
  }

  test("Test direct methods: TlaSeqOper") {
    val appendBuild = bd.append(n_a, n_b).untyped()

    assert(appendBuild == OperEx(TlaSeqOper.append, n_a, n_b))

    val concatBuild = bd.concat(n_a, n_b).untyped()

    assert(concatBuild == OperEx(TlaSeqOper.concat, n_a, n_b))

    val headBuild = bd.head(n_a).untyped()

    assert(headBuild == OperEx(TlaSeqOper.head, n_a))

    val tailBuild = bd.tail(n_a).untyped()

    assert(tailBuild == OperEx(TlaSeqOper.tail, n_a))

    val lenBuild = bd.len(n_a).untyped()

    assert(lenBuild == OperEx(TlaSeqOper.len, n_a))
  }

  test("Test byName: TlaSeqOper") {
    val appendBuild = bd.byName(TlaSeqOper.append.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.append.name, n_a).untyped())
    assert(appendBuild == OperEx(TlaSeqOper.append, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.append.name, n_a, n_b, n_c).untyped())

    val concatBuild = bd.byName(TlaSeqOper.concat.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.concat.name, n_a).untyped())
    assert(concatBuild == OperEx(TlaSeqOper.concat, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.concat.name, n_a, n_b, n_c).untyped())

    val headBuild = bd.byName(TlaSeqOper.head.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.head.name).untyped())
    assert(headBuild == OperEx(TlaSeqOper.head, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.head.name, n_a, n_b).untyped())

    val tailBuild = bd.byName(TlaSeqOper.tail.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.tail.name).untyped())
    assert(tailBuild == OperEx(TlaSeqOper.tail, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.tail.name, n_a, n_b).untyped())

    val lenBuild = bd.byName(TlaSeqOper.len.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.len.name).untyped())
    assert(lenBuild == OperEx(TlaSeqOper.len, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.len.name, n_a, n_b).untyped())
  }

  test("Test byNameOrNull: TlaSeqOper") {
    val appendBuildBad1 = bd.byNameOrNull(TlaSeqOper.append.name, n_a).untyped()
    val appendBuild = bd.byNameOrNull(TlaSeqOper.append.name, n_a, n_b).untyped()
    val appendBuildBad2 = bd.byNameOrNull(TlaSeqOper.append.name, n_a, n_b, n_c).untyped()

    assert(appendBuildBad1 == NullEx)
    assert(appendBuild == OperEx(TlaSeqOper.append, n_a, n_b))
    assert(appendBuildBad2 == NullEx)

    val concatBuildBad1 = bd.byNameOrNull(TlaSeqOper.concat.name, n_a).untyped()
    val concatBuild = bd.byNameOrNull(TlaSeqOper.concat.name, n_a, n_b).untyped()
    val concatBuildBad2 = bd.byNameOrNull(TlaSeqOper.concat.name, n_a, n_b, n_c).untyped()

    assert(concatBuildBad1 == NullEx)
    assert(concatBuild == OperEx(TlaSeqOper.concat, n_a, n_b))
    assert(concatBuildBad2 == NullEx)

    val headBuildBad1 = bd.byNameOrNull(TlaSeqOper.head.name).untyped()
    val headBuild = bd.byNameOrNull(TlaSeqOper.head.name, n_a).untyped()
    val headBuildBad2 = bd.byNameOrNull(TlaSeqOper.head.name, n_a, n_b).untyped()

    assert(headBuildBad1 == NullEx)
    assert(headBuild == OperEx(TlaSeqOper.head, n_a))
    assert(headBuildBad2 == NullEx)

    val tailBuildBad1 = bd.byNameOrNull(TlaSeqOper.tail.name).untyped()
    val tailBuild = bd.byNameOrNull(TlaSeqOper.tail.name, n_a).untyped()
    val tailBuildBad2 = bd.byNameOrNull(TlaSeqOper.tail.name, n_a, n_b).untyped()

    assert(tailBuildBad1 == NullEx)
    assert(tailBuild == OperEx(TlaSeqOper.tail, n_a))
    assert(tailBuildBad2 == NullEx)

    val lenBuildBad1 = bd.byNameOrNull(TlaSeqOper.len.name).untyped()
    val lenBuild = bd.byNameOrNull(TlaSeqOper.len.name, n_a).untyped()
    val lenBuildBad2 = bd.byNameOrNull(TlaSeqOper.len.name, n_a, n_b).untyped()

    assert(lenBuildBad1 == NullEx)
    assert(lenBuild == OperEx(TlaSeqOper.len, n_a))
    assert(lenBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaSetOper") {
    val enumSetBuild1 = bd.enumSet().untyped()
    val enumSetBuild2 = bd.enumSet(n_a, n_b).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, n_a, n_b))

    val inBuild = bd.in(n_a, n_b).untyped()

    assert(inBuild == OperEx(TlaSetOper.in, n_a, n_b))

    val notinBuild = bd.notin(n_a, n_b).untyped()

    assert(notinBuild == OperEx(TlaSetOper.notin, n_a, n_b))

    val capBuild = bd.cap(n_a, n_b).untyped()

    assert(capBuild == OperEx(TlaSetOper.cap, n_a, n_b))

    val cupBuild = bd.cup(n_a, n_b).untyped()

    assert(cupBuild == OperEx(TlaSetOper.cup, n_a, n_b))

    val unionBuild = bd.union(n_a).untyped()

    assert(unionBuild == OperEx(TlaSetOper.union, n_a))

    val filterBuild = bd.filter(n_a, n_b, n_c).untyped()

    assert(filterBuild == OperEx(TlaSetOper.filter, n_a, n_b, n_c))

    val mapBuild1 = bd.map(n_a, n_b, n_c).untyped()
    val mapBuild2 = bd.map(n_a, n_b, n_c, n_d, n_e).untyped()

    assert(mapBuild1 == OperEx(TlaSetOper.map, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.map(n_a, n_b, n_c, n_d).untyped())
    assert(mapBuild2 == OperEx(TlaSetOper.map, n_a, n_b, n_c, n_d, n_e))
    assertThrows[IllegalArgumentException](bd.map(n_a, n_b, n_c, n_d, n_e, n_f).untyped())

    val funSetBuild = bd.funSet(n_a, n_b).untyped()

    assert(funSetBuild == OperEx(TlaSetOper.funSet, n_a, n_b))

    val recSetBuild1 = bd.recSet().untyped()
    val recSetBuild2 = bd.recSet(n_a, n_b).untyped()

    assert(recSetBuild1 == OperEx(TlaSetOper.recSet))
    assertThrows[IllegalArgumentException](bd.recSet(n_a).untyped())
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.recSet(n_a, n_b, n_c).untyped())

    val seqSetBuild = bd.seqSet(n_a).untyped()

    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, n_a))

    val subseteqBuild = bd.subseteq(n_a, n_b).untyped()
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, n_a, n_b))

    val setminusBuild = bd.setminus(n_a, n_b).untyped()

    assert(setminusBuild == OperEx(TlaSetOper.setminus, n_a, n_b))

    val timesBuild1 = bd.times().untyped()
    val timesBuild2 = bd.times(n_a, n_b).untyped()

    assert(timesBuild1 == OperEx(TlaSetOper.times))
    assert(timesBuild2 == OperEx(TlaSetOper.times, n_a, n_b))

    val powSetBuild = bd.powSet(n_a).untyped()

    assert(powSetBuild == OperEx(TlaSetOper.powerset, n_a))
  }

  test("Test byName: TlaSetOper") {
    val enumSetBuild1 = bd.byName(TlaSetOper.enumSet.name).untyped()
    val enumSetBuild2 = bd.byName(TlaSetOper.enumSet.name, n_a, n_b).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, n_a, n_b))

    val inBuild = bd.byName(TlaSetOper.in.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.in.name, n_a).untyped())
    assert(inBuild == OperEx(TlaSetOper.in, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.in.name, n_a, n_b, n_c).untyped())

    val notinBuild = bd.byName(TlaSetOper.notin.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.notin.name, n_a).untyped())
    assert(notinBuild == OperEx(TlaSetOper.notin, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.notin.name, n_a, n_b, n_c).untyped())

    val capBuild = bd.byName(TlaSetOper.cap.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cap.name, n_a).untyped())
    assert(capBuild == OperEx(TlaSetOper.cap, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cap.name, n_a, n_b, n_c).untyped())

    val cupBuild = bd.byName(TlaSetOper.cup.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cup.name, n_a).untyped())
    assert(cupBuild == OperEx(TlaSetOper.cup, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cup.name, n_a, n_b, n_c).untyped())

    val unionBuild = bd.byName(TlaSetOper.union.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.union.name).untyped())
    assert(unionBuild == OperEx(TlaSetOper.union, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.union.name, n_a, n_b).untyped())

    val filterBuild = bd.byName(TlaSetOper.filter.name, n_a, n_b, n_c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.filter.name, n_a, n_b).untyped())
    assert(filterBuild == OperEx(TlaSetOper.filter, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.filter.name, n_a, n_b, n_c, n_d).untyped())

    val mapBuild1 = bd.byNameOrNull(TlaSetOper.map.name, n_a, n_b, n_c).untyped()
    val mapBuild2 = bd.byNameOrNull(TlaSetOper.map.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.map.name, n_a, n_b).untyped())
    assert(mapBuild1 == OperEx(TlaSetOper.map, n_a, n_b, n_c))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.map.name, n_a, n_b, n_c, n_d).untyped())
    assert(mapBuild2 == OperEx(TlaSetOper.map, n_a, n_b, n_c, n_d, n_e))

    val funSetBuild = bd.byName(TlaSetOper.funSet.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.funSet.name, n_a).untyped())
    assert(funSetBuild == OperEx(TlaSetOper.funSet, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.funSet.name, n_a, n_b, n_c).untyped())

    val recSetBuild1 = bd.byNameOrNull(TlaSetOper.recSet.name).untyped()
    val recSetBuild2 = bd.byNameOrNull(TlaSetOper.recSet.name, n_a, n_b).untyped()

    assert(recSetBuild1 == OperEx(TlaSetOper.recSet))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, n_a).untyped())
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, n_a, n_b, n_c).untyped())

    val seqSetBuild = bd.byName(TlaSetOper.seqSet.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.seqSet.name).untyped())
    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.seqSet.name, n_a, n_b).untyped())

    val subseteqBuild = bd.byName(TlaSetOper.subseteq.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.subseteq.name, n_a).untyped())
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.subseteq.name, n_a, n_b, n_c).untyped())

    val setminusBuild = bd.byName(TlaSetOper.setminus.name, n_a, n_b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.setminus.name, n_a).untyped())
    assert(setminusBuild == OperEx(TlaSetOper.setminus, n_a, n_b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.setminus.name, n_a, n_b, n_c).untyped())

    val timesBuild1 = bd.byName(TlaSetOper.times.name).untyped()
    val timesBuild2 = bd.byName(TlaSetOper.times.name, n_a, n_b).untyped()

    assert(timesBuild1 == OperEx(TlaSetOper.times))
    assert(timesBuild2 == OperEx(TlaSetOper.times, n_a, n_b))

    val powSetBuild = bd.byName(TlaSetOper.powerset.name, n_a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.powerset.name).untyped())
    assert(powSetBuild == OperEx(TlaSetOper.powerset, n_a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.powerset.name, n_a, n_b).untyped())

  }

  test("Test byNameOrNull: TlaSetOper") {
    val enumSetBuild1 = bd.byNameOrNull(TlaSetOper.enumSet.name).untyped()
    val enumSetBuild2 = bd.byNameOrNull(TlaSetOper.enumSet.name, n_a, n_b).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, n_a, n_b))

    val inBuildBad1 = bd.byNameOrNull(TlaSetOper.in.name, n_a).untyped()
    val inBuild = bd.byNameOrNull(TlaSetOper.in.name, n_a, n_b).untyped()
    val inBuildBad2 = bd.byNameOrNull(TlaSetOper.in.name, n_a, n_b, n_c).untyped()

    assert(inBuildBad1 == NullEx)
    assert(inBuild == OperEx(TlaSetOper.in, n_a, n_b))
    assert(inBuildBad2 == NullEx)

    val notinBuildBad1 = bd.byNameOrNull(TlaSetOper.notin.name, n_a).untyped()
    val notinBuild = bd.byNameOrNull(TlaSetOper.notin.name, n_a, n_b).untyped()
    val notinBuildBad2 = bd.byNameOrNull(TlaSetOper.notin.name, n_a, n_b, n_c).untyped()

    assert(notinBuildBad1 == NullEx)
    assert(notinBuild == OperEx(TlaSetOper.notin, n_a, n_b))
    assert(notinBuildBad2 == NullEx)

    val capBuildBad1 = bd.byNameOrNull(TlaSetOper.cap.name, n_a).untyped()
    val capBuild = bd.byNameOrNull(TlaSetOper.cap.name, n_a, n_b).untyped()
    val capBuildBad2 = bd.byNameOrNull(TlaSetOper.cap.name, n_a, n_b, n_c).untyped()

    assert(capBuildBad1 == NullEx)
    assert(capBuild == OperEx(TlaSetOper.cap, n_a, n_b))
    assert(capBuildBad2 == NullEx)

    val cupBuildBad1 = bd.byNameOrNull(TlaSetOper.cup.name, n_a).untyped()
    val cupBuild = bd.byNameOrNull(TlaSetOper.cup.name, n_a, n_b).untyped()
    val cupBuildBad2 = bd.byNameOrNull(TlaSetOper.cup.name, n_a, n_b, n_c).untyped()

    assert(cupBuildBad1 == NullEx)
    assert(cupBuild == OperEx(TlaSetOper.cup, n_a, n_b))
    assert(cupBuildBad2 == NullEx)

    val unionBuildBad1 = bd.byNameOrNull(TlaSetOper.union.name).untyped()
    val unionBuild = bd.byNameOrNull(TlaSetOper.union.name, n_a).untyped()
    val unionBuildBad2 = bd.byNameOrNull(TlaSetOper.union.name, n_a, n_b).untyped()

    assert(unionBuildBad1 == NullEx)
    assert(unionBuild == OperEx(TlaSetOper.union, n_a))
    assert(unionBuildBad2 == NullEx)

    val filterBuildBad1 = bd.byNameOrNull(TlaSetOper.filter.name, n_a, n_b).untyped()
    val filterBuild = bd.byNameOrNull(TlaSetOper.filter.name, n_a, n_b, n_c).untyped()
    val filterBuildBad2 = bd.byNameOrNull(TlaSetOper.filter.name, n_a, n_b, n_c, n_d).untyped()

    assert(filterBuildBad1 == NullEx)
    assert(filterBuild == OperEx(TlaSetOper.filter, n_a, n_b, n_c))
    assert(filterBuildBad2 == NullEx)

    val mapBuildBad1 = bd.byNameOrNull(TlaSetOper.map.name, n_a, n_b).untyped()
    val mapBuild1 = bd.byNameOrNull(TlaSetOper.map.name, n_a, n_b, n_c).untyped()
    val mapBuildBad2 = bd.byNameOrNull(TlaSetOper.map.name, n_a, n_b, n_c, n_d).untyped()
    val mapBuild2 = bd.byNameOrNull(TlaSetOper.map.name, n_a, n_b, n_c, n_d, n_e).untyped()

    assert(mapBuildBad1 == NullEx)
    assert(mapBuild1 == OperEx(TlaSetOper.map, n_a, n_b, n_c))
    assert(mapBuildBad2 == NullEx)
    assert(mapBuild2 == OperEx(TlaSetOper.map, n_a, n_b, n_c, n_d, n_e))

    val funSetBuildBad1 = bd.byNameOrNull(TlaSetOper.funSet.name, n_a).untyped()
    val funSetBuild = bd.byNameOrNull(TlaSetOper.funSet.name, n_a, n_b).untyped()
    val funSetBuildBad2 = bd.byNameOrNull(TlaSetOper.funSet.name, n_a, n_b, n_c).untyped()

    assert(funSetBuildBad1 == NullEx)
    assert(funSetBuild == OperEx(TlaSetOper.funSet, n_a, n_b))
    assert(funSetBuildBad2 == NullEx)

    val recSetBuild1 = bd.byNameOrNull(TlaSetOper.recSet.name).untyped()
    val recSetBuildBad1 = bd.byNameOrNull(TlaSetOper.recSet.name, n_a).untyped()
    val recSetBuild2 = bd.byNameOrNull(TlaSetOper.recSet.name, n_a, n_b).untyped()
    val recSetBuildBad2 = bd.byNameOrNull(TlaSetOper.recSet.name, n_a, n_b, n_c).untyped()

    assert(recSetBuild1 == OperEx(TlaSetOper.recSet))
    assert(recSetBuildBad1 == NullEx)
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, n_a, n_b))
    assert(recSetBuildBad2 == NullEx)

    val seqSetBuildBad1 = bd.byNameOrNull(TlaSetOper.seqSet.name).untyped()
    val seqSetBuild = bd.byNameOrNull(TlaSetOper.seqSet.name, n_a).untyped()
    val seqSetBuildBad2 = bd.byNameOrNull(TlaSetOper.seqSet.name, n_a, n_b).untyped()

    assert(seqSetBuildBad1 == NullEx)
    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, n_a))
    assert(seqSetBuildBad2 == NullEx)

    val subseteqBuildBad1 = bd.byNameOrNull(TlaSetOper.subseteq.name, n_a).untyped()
    val subseteqBuild = bd.byNameOrNull(TlaSetOper.subseteq.name, n_a, n_b).untyped()
    val subseteqBuildBad2 = bd.byNameOrNull(TlaSetOper.subseteq.name, n_a, n_b, n_c).untyped()

    assert(subseteqBuildBad1 == NullEx)
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, n_a, n_b))
    assert(subseteqBuildBad2 == NullEx)

    val setminusBuildBad1 = bd.byNameOrNull(TlaSetOper.setminus.name, n_a).untyped()
    val setminusBuild = bd.byNameOrNull(TlaSetOper.setminus.name, n_a, n_b).untyped()
    val setminusBuildBad2 = bd.byNameOrNull(TlaSetOper.setminus.name, n_a, n_b, n_c).untyped()

    assert(setminusBuildBad1 == NullEx)
    assert(setminusBuild == OperEx(TlaSetOper.setminus, n_a, n_b))
    assert(setminusBuildBad2 == NullEx)

    val timesBuild1 = bd.byNameOrNull(TlaSetOper.times.name).untyped()
    val timesBuild2 = bd.byNameOrNull(TlaSetOper.times.name, n_a, n_b).untyped()

    assert(timesBuild1 == OperEx(TlaSetOper.times))
    assert(timesBuild2 == OperEx(TlaSetOper.times, n_a, n_b))

    val powersetBuildBad1 = bd.byNameOrNull(TlaSetOper.powerset.name).untyped()
    val powersetBuild = bd.byNameOrNull(TlaSetOper.powerset.name, n_a).untyped()
    val powersetBuildBad2 = bd.byNameOrNull(TlaSetOper.powerset.name, n_a, n_b).untyped()

    assert(powersetBuildBad1 == NullEx)
    assert(powersetBuild == OperEx(TlaSetOper.powerset, n_a))
    assert(powersetBuildBad2 == NullEx)

  }

  test("Test direct methods: TlctOper") {
    val assertMsg = "None"
    val assertion = bd.tlcAssert(NullEx, assertMsg).untyped()

    assert(assertion == OperEx(TlcOper.assert, NullEx, bd.str(assertMsg)))
  }

}

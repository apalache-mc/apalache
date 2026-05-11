package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla

@RunWith(classOf[JUnitRunner])
class TestBuilder extends AnyFunSuite {
  private val bd = new Builder()

  test("Test direct methods: Names and values") {
    val a = NameEx("a")
    val nameBuild: TlaEx = bd.name("a")

    assert(nameBuild == a)

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
    val c = NameEx("c")
    val x = NameEx("x")
    val B = NameEx("B")
    val a = NameEx("a")
    val b = NameEx("b")
    val decl1 = bd.declOp("A", c).untypedOperDecl()
    val decl2 = bd.declOp("A", x, OperParam("x")).untypedOperDecl()
    val decl3 = bd.declOp("A", bd.appOp(B), OperParam("B", 0)).untypedOperDecl()
    val decl4 = bd.declOp("A", bd.appOp(B, x), OperParam("x"), OperParam("B", 1)).untypedOperDecl()

    assert(decl1 == TlaOperDecl("A", List(), c))
    assert(decl2 == TlaOperDecl("A", List(OperParam("x")), x))
    assert(decl3 ==
      TlaOperDecl(
          "A",
          List(OperParam("B", 0)),
          OperEx(TlaOper.apply, B),
      ))
    assert(decl4 ==
      TlaOperDecl(
          "A",
          List(OperParam("x"), OperParam("B", 1)),
          OperEx(TlaOper.apply, B, x),
      ))

    val appEx1 = bd.appDecl(decl1).untyped()
    val appEx2 = bd.appDecl(decl2, a).untyped()
    val appEx3 = bd.appDecl(decl3, a).untyped()
    val appEx4 = bd.appDecl(decl4, a, b).untyped()

    assert(appEx1 == OperEx(TlaOper.apply, tla.name(decl1.name)))
    assertThrows[IllegalArgumentException](bd.appDecl(decl1, a))
    assertThrows[IllegalArgumentException](bd.appDecl(decl2))
    assert(appEx2 == OperEx(TlaOper.apply, tla.name(decl2.name), a))
    assertThrows[IllegalArgumentException](bd.appDecl(decl2, a, b))
    assertThrows[IllegalArgumentException](bd.appDecl(decl3))
    assert(appEx3 == OperEx(TlaOper.apply, tla.name(decl3.name), a))
    assertThrows[IllegalArgumentException](bd.appDecl(decl3, a, b))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4, a))
    assert(appEx4 == OperEx(TlaOper.apply, tla.name(decl4.name), a, b))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4, a, b, c))
  }

  test("Test byName: bad calls") {
    val b = NameEx("b")
    assertThrows[NoSuchElementException](bd.byName("not an operator name", NullEx, b))

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, NullEx).untyped())
  }

  test("Test byNameOrNull: bad calls") {
    val b = NameEx("b")
    val nullBadName = bd.byNameOrNull("not an operator name", NullEx, b).untyped()

    assert(nullBadName == NullEx)

    val nullBadArity = bd.byNameOrNull(TlaArithOper.plus.name, NullEx).untyped()

    assert(nullBadArity == NullEx)
  }

  test("Test direct methods: TlaOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val S = NameEx("S")
    val eqBuild1 = bd.eql(a, b).untyped()
    val eqBuild2 = bd.eql(a, bd.int(2)).untyped()

    assert(eqBuild1 == OperEx(TlaOper.eq, a, b))
    assert(eqBuild2 == OperEx(TlaOper.eq, a, ValEx(TlaInt(2))))

    val neBuild1 = bd.neql(a, b).untyped()
    val neBuild2 = bd.neql(a, bd.int(2)).untyped()

    assert(neBuild1 == OperEx(TlaOper.ne, a, b))
    assert(neBuild2 == OperEx(TlaOper.ne, a, ValEx(TlaInt(2))))

    val applyBuild1 = bd.appOp(a).untyped()
    val applyBuild2 = bd.appOp(a, b).untyped()
    val applyBuild3 = bd.appOp(a, b, c).untyped()
    val applyBuild4 = bd.appOp(a, b, c, d).untyped()

    assert(applyBuild1 == OperEx(TlaOper.apply, a))
    assert(applyBuild2 == OperEx(TlaOper.apply, a, b))
    assert(applyBuild3 == OperEx(TlaOper.apply, a, b, c))
    assert(applyBuild4 == OperEx(TlaOper.apply, a, b, c, d))

    val chooseBuild1 = bd.choose(a, b).untyped()
    val chooseBuild2 = bd.choose(a, b, c).untyped()

    assert(chooseBuild1 == OperEx(TlaOper.chooseUnbounded, a, b))
    assert(chooseBuild2 == OperEx(TlaOper.chooseBounded, a, b, c))

    val guessBuild = bd.guess(S).untyped()
    assert(guessBuild == OperEx(ApalacheOper.guess, S))
  }

  test("Test byName: TlaOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val eqBuild = bd.byName(TlaOper.eq.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.eq.name, a).untyped())
    assert(eqBuild == OperEx(TlaOper.eq, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.eq.name, a, b, c).untyped())

    val neBuild = bd.byName(TlaOper.ne.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.ne.name, a).untyped())
    assert(neBuild == OperEx(TlaOper.ne, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.ne.name, a, b, c).untyped())

    val cbBuild = bd.byName(TlaOper.chooseBounded.name, a, b, c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseBounded.name, a, b).untyped())
    assert(cbBuild == OperEx(TlaOper.chooseBounded, a, b, c))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseBounded.name, a, b, c, d).untyped())

    val cubBuild = bd.byName(TlaOper.chooseUnbounded.name, a, b).untyped()

    assert(cubBuild == OperEx(TlaOper.chooseUnbounded, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseUnbounded.name, a, b, c).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseUnbounded.name, a, b, c, d).untyped())
  }

  test("Test byNameOrNull: TlaOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val eqBuildBad1 = bd.byNameOrNull(TlaOper.eq.name, a).untyped()
    val eqBuild = bd.byNameOrNull(TlaOper.eq.name, a, b).untyped()
    val eqBuildBad2 = bd.byNameOrNull(TlaOper.eq.name, a, b, c).untyped()

    assert(eqBuildBad1 == NullEx)
    assert(eqBuild == OperEx(TlaOper.eq, a, b))
    assert(eqBuildBad2 == NullEx)

    val neBuildBad1 = bd.byNameOrNull(TlaOper.ne.name, a).untyped()
    val neBuild = bd.byNameOrNull(TlaOper.ne.name, a, b).untyped()
    val neBuildBad2 = bd.byNameOrNull(TlaOper.ne.name, a, b, c).untyped()

    assert(neBuildBad1 == NullEx)
    assert(neBuild == OperEx(TlaOper.ne, a, b))
    assert(neBuildBad2 == NullEx)

    val cbBuildBad1 = bd.byNameOrNull(TlaOper.chooseBounded.name, a, b).untyped()
    val cbBuild = bd.byNameOrNull(TlaOper.chooseBounded.name, a, b, c).untyped()
    val cbBuildBad2 = bd.byNameOrNull(TlaOper.chooseBounded.name, a, b, c, d).untyped()

    assert(cbBuildBad1 == NullEx)
    assert(cbBuild == OperEx(TlaOper.chooseBounded, a, b, c))
    assert(cbBuildBad2 == NullEx)

    val cubBuild = bd.byNameOrNull(TlaOper.chooseUnbounded.name, a, b).untyped()
    val cubBuildBad1 = bd.byNameOrNull(TlaOper.chooseUnbounded.name, a, b, c).untyped()
    val cubBuildBad2 = bd.byNameOrNull(TlaOper.chooseUnbounded.name, a, b, c, d).untyped()

    assert(cubBuild == OperEx(TlaOper.chooseUnbounded, a, b))
    assert(cubBuildBad1 == NullEx)
    assert(cubBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaBoolOper ") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val andBuild1 = bd.and(a).untyped()
    val andBuild2 = bd.and(a, b).untyped()
    val andBuild3 = bd.and(a, b, c).untyped()
    val andBuild4 = bd.and(a, b, c, d).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and, a))
    assert(andBuild2 == OperEx(TlaBoolOper.and, a, b))
    assert(andBuild3 == OperEx(TlaBoolOper.and, a, b, c))
    assert(andBuild4 == OperEx(TlaBoolOper.and, a, b, c, d))

    val orBuild1 = bd.or(a).untyped()
    val orBuild2 = bd.or(a, b).untyped()
    val orBuild3 = bd.or(a, b, c).untyped()
    val orBuild4 = bd.or(a, b, c, d).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or, a))
    assert(orBuild2 == OperEx(TlaBoolOper.or, a, b))
    assert(orBuild3 == OperEx(TlaBoolOper.or, a, b, c))
    assert(orBuild4 == OperEx(TlaBoolOper.or, a, b, c, d))

    val notBuild1 = bd.not(a).untyped()

    assert(notBuild1 == OperEx(TlaBoolOper.not, a))

    val impliesBuild1 = bd.impl(a, b).untyped()

    assert(impliesBuild1 == OperEx(TlaBoolOper.implies, a, b))

    val equivBuild1 = bd.equiv(a, b).untyped()

    assert(equivBuild1 == OperEx(TlaBoolOper.equiv, a, b))

    val forallBuild1 = bd.forall(a, b).untyped()
    val forallBuild2 = bd.forall(a, b, c).untyped()

    assert(forallBuild1 == OperEx(TlaBoolOper.forallUnbounded, a, b))
    assert(forallBuild2 == OperEx(TlaBoolOper.forall, a, b, c))

    val existsBuild1 = bd.exists(a, b).untyped()
    val existsBuild2 = bd.exists(a, b, c).untyped()

    assert(existsBuild1 == OperEx(TlaBoolOper.existsUnbounded, a, b))
    assert(existsBuild2 == OperEx(TlaBoolOper.exists, a, b, c))
  }

  test("Test byName: TlaBoolOper ") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val andBuild1 = bd.byName(TlaBoolOper.and.name).untyped()
    val andBuild2 = bd.byName(TlaBoolOper.and.name, a).untyped()
    val andBuild3 = bd.byName(TlaBoolOper.and.name, a, b).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and))
    assert(andBuild2 == OperEx(TlaBoolOper.and, a))
    assert(andBuild3 == OperEx(TlaBoolOper.and, a, b))

    val orBuild1 = bd.byName(TlaBoolOper.or.name).untyped()
    val orBuild2 = bd.byName(TlaBoolOper.or.name, a).untyped()
    val orBuild3 = bd.byName(TlaBoolOper.or.name, a, b).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or))
    assert(orBuild2 == OperEx(TlaBoolOper.or, a))
    assert(orBuild3 == OperEx(TlaBoolOper.or, a, b))

    val notBuild = bd.byName(TlaBoolOper.not.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.not.name).untyped())
    assert(notBuild == OperEx(TlaBoolOper.not, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.not.name, a, b).untyped())

    val impliesBuild = bd.byName(TlaBoolOper.implies.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.implies.name, a).untyped())
    assert(impliesBuild == OperEx(TlaBoolOper.implies, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.implies.name, a, b, c).untyped())

  }

  test("Test byNameOrNull: TlaBoolOper ") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val andBuild1 = bd.byNameOrNull(TlaBoolOper.and.name).untyped()
    val andBuild2 = bd.byNameOrNull(TlaBoolOper.and.name, a).untyped()
    val andBuild3 = bd.byNameOrNull(TlaBoolOper.and.name, a, b).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and))
    assert(andBuild2 == OperEx(TlaBoolOper.and, a))
    assert(andBuild3 == OperEx(TlaBoolOper.and, a, b))

    val orBuild1 = bd.byNameOrNull(TlaBoolOper.or.name).untyped()
    val orBuild2 = bd.byNameOrNull(TlaBoolOper.or.name, a).untyped()
    val orBuild3 = bd.byNameOrNull(TlaBoolOper.or.name, a, b).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or))
    assert(orBuild2 == OperEx(TlaBoolOper.or, a))
    assert(orBuild3 == OperEx(TlaBoolOper.or, a, b))

    val notBuildBad1 = bd.byNameOrNull(TlaBoolOper.not.name).untyped()
    val notBuild = bd.byNameOrNull(TlaBoolOper.not.name, a).untyped()
    val notBuildBad2 = bd.byNameOrNull(TlaBoolOper.not.name, a, b).untyped()

    assert(notBuildBad1 == NullEx)
    assert(notBuild == OperEx(TlaBoolOper.not, a))
    assert(notBuildBad2 == NullEx)

    val impliesBuildBad1 = bd.byNameOrNull(TlaBoolOper.implies.name, a).untyped()
    val impliesBuild = bd.byNameOrNull(TlaBoolOper.implies.name, a, b).untyped()
    val impliesBuildBad2 = bd.byNameOrNull(TlaBoolOper.implies.name, a, b, c).untyped()

    assert(impliesBuildBad1 == NullEx)
    assert(impliesBuild == OperEx(TlaBoolOper.implies, a, b))
    assert(impliesBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaActionOper") {
    val a = NameEx("a")
    val name = NameEx("name")
    val b = NameEx("b")
    val name1 = NameEx("name1")
    val name2 = NameEx("name2")
    val primeBuild1 = bd.prime(a).untyped()
    val primeBuild2 = bd.prime(bd.name("name")).untyped()

    assert(primeBuild1 == OperEx(TlaActionOper.prime, a))
    assert(primeBuild2 == OperEx(TlaActionOper.prime, name))

    val primeEqBuild1 = bd.primeEq(bd.name("name"), a).untyped()
    val primeEqBuild2 = bd.primeEq(a, b).untyped()
    val primeEqBuild3 = bd.primeEq(bd.name("name"), bd.int(1)).untyped()
    val primeEqBuild4 = bd.primeEq(a, bd.int(2)).untyped()
    val primeEqBuild5 = bd.primeEq(bd.name("name1"), bd.name("name2")).untyped()

    assert(primeEqBuild1 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, name), a))
    assert(primeEqBuild2 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, a), b))
    assert(primeEqBuild3 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, name), ValEx(TlaInt(1))))
    assert(primeEqBuild4 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, a), ValEx(TlaInt(2))))
    assert(primeEqBuild5 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, name1), name2))

    val stutterBuild = bd.stutt(a, b).untyped()

    assert(stutterBuild == OperEx(TlaActionOper.stutter, a, b))

    val nostutterBuild = bd.nostutt(a, b).untyped()

    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, a, b))

    val enabledBuild = bd.enabled(a).untyped()

    assert(enabledBuild == OperEx(TlaActionOper.enabled, a))

    val unchangedBuild = bd.unchanged(a).untyped()

    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, a))

    val compositionBuild = bd.comp(a, b).untyped()

    assert(compositionBuild == OperEx(TlaActionOper.composition, a, b))

  }

  test("Test byName: TlaActionOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val primeBuild = bd.byNameOrNull(TlaActionOper.prime.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.prime.name).untyped())
    assert(primeBuild == OperEx(TlaActionOper.prime, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.prime.name, a, b).untyped())

    val stutterBuild = bd.byName(TlaActionOper.stutter.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.stutter.name, a).untyped())
    assert(stutterBuild == OperEx(TlaActionOper.stutter, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.stutter.name, a, b, c).untyped())

    val nostutterBuild = bd.byName(TlaActionOper.nostutter.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.nostutter.name, a).untyped())
    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.nostutter.name, a, b, c).untyped())

    val enabledBuild = bd.byName(TlaActionOper.enabled.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.enabled.name).untyped())
    assert(enabledBuild == OperEx(TlaActionOper.enabled, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.enabled.name, a, b).untyped())

    val unchangedBuild = bd.byName(TlaActionOper.unchanged.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.unchanged.name).untyped())
    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.unchanged.name, a, b).untyped())

    val compositionBuild = bd.byName(TlaActionOper.composition.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.composition.name, a).untyped())
    assert(compositionBuild == OperEx(TlaActionOper.composition, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.composition.name, a, b, c).untyped())
  }

  test("Test byNameOrNull: TlaActionOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val primeBuildBad1 = bd.byNameOrNull(TlaActionOper.prime.name).untyped()
    val primeBuild = bd.byNameOrNull(TlaActionOper.prime.name, a).untyped()
    val primeBuildBad2 = bd.byNameOrNull(TlaActionOper.prime.name, a, b).untyped()

    assert(primeBuildBad1 == NullEx)
    assert(primeBuild == OperEx(TlaActionOper.prime, a))
    assert(primeBuildBad2 == NullEx)

    val stutterBuildBad1 = bd.byNameOrNull(TlaActionOper.stutter.name, a).untyped()
    val stutterBuild = bd.byNameOrNull(TlaActionOper.stutter.name, a, b).untyped()
    val stutterBuildBad2 = bd.byNameOrNull(TlaActionOper.stutter.name, a, b, c).untyped()

    assert(stutterBuildBad1 == NullEx)
    assert(stutterBuild == OperEx(TlaActionOper.stutter, a, b))
    assert(stutterBuildBad2 == NullEx)

    val nostutterBuildBad1 = bd.byNameOrNull(TlaActionOper.nostutter.name, a).untyped()
    val nostutterBuild = bd.byNameOrNull(TlaActionOper.nostutter.name, a, b).untyped()
    val nostutterBuildBad2 = bd.byNameOrNull(TlaActionOper.nostutter.name, a, b, c).untyped()

    assert(nostutterBuildBad1 == NullEx)
    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, a, b))
    assert(nostutterBuildBad2 == NullEx)

    val enabledBuildBad1 = bd.byNameOrNull(TlaActionOper.enabled.name).untyped()
    val enabledBuild = bd.byNameOrNull(TlaActionOper.enabled.name, a).untyped()
    val enabledBuildBad2 = bd.byNameOrNull(TlaActionOper.enabled.name, a, b).untyped()

    assert(enabledBuildBad1 == NullEx)
    assert(enabledBuild == OperEx(TlaActionOper.enabled, a))
    assert(enabledBuildBad2 == NullEx)

    val unchangedBuildBad1 = bd.byNameOrNull(TlaActionOper.unchanged.name).untyped()
    val unchangedBuild = bd.byNameOrNull(TlaActionOper.unchanged.name, a).untyped()
    val unchangedBuildBad2 = bd.byNameOrNull(TlaActionOper.unchanged.name, a, b).untyped()

    assert(unchangedBuildBad1 == NullEx)
    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, a))
    assert(unchangedBuildBad2 == NullEx)

    val compositionBuildBad1 = bd.byNameOrNull(TlaActionOper.composition.name, a).untyped()
    val compositionBuild = bd.byNameOrNull(TlaActionOper.composition.name, a, b).untyped()
    val compositionBuildBad2 = bd.byNameOrNull(TlaActionOper.composition.name, a, b, c).untyped()

    assert(compositionBuildBad1 == NullEx)
    assert(compositionBuild == OperEx(TlaActionOper.composition, a, b))
    assert(compositionBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaControlOper") {

    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val f = NameEx("f")
    val g = NameEx("g")
    val caseBuild1 = bd.caseAny(a, b).untyped()
    val caseBuild2 = bd.caseAny(a, b, c).untyped()
    val caseBuild3 = bd.caseAny(a, b, c, d).untyped()
    val caseBuild4 = bd.caseAny(a, b, c, d, e).untyped()
    val caseBuild5 = bd.caseAny(a, b, c, d, e, f).untyped()
    val caseBuild6 = bd.caseAny(a, b, c, d, e, f, g).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, a, b))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, a, b, c))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, a, b, c, d))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, a, b, c, d, e, f))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e, f, g))

    val caseSplitBuild1 = bd.caseSplit(a, b).untyped()
    val caseSplitBuild2 = bd.caseSplit(a, b, c, d).untyped()
    val caseSplitBuild3 = bd.caseSplit(a, b, c, d, e, f).untyped()

    assert(caseSplitBuild1 == OperEx(TlaControlOper.caseNoOther, a, b))
    assertThrows[IllegalArgumentException](bd.caseSplit(a, b, c).untyped())
    assert(caseSplitBuild2 == OperEx(TlaControlOper.caseNoOther, a, b, c, d))
    assertThrows[IllegalArgumentException](bd.caseSplit(a, b, c, d, e).untyped())
    assert(caseSplitBuild3 == OperEx(TlaControlOper.caseNoOther, a, b, c, d, e, f))

    val caseOtherBuild1 = bd.caseOther(a, b, c).untyped()
    val caseOtherBuild2 = bd.caseOther(a, b, c, d, e).untyped()
    val caseOtherBuild3 = bd.caseOther(a, b, c, d, e, f, g).untyped()

    assert(caseOtherBuild1 == OperEx(TlaControlOper.caseWithOther, a, b, c))
    assertThrows[IllegalArgumentException](bd.caseOther(a, b, c, d).untyped())
    assert(caseOtherBuild2 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e))
    assertThrows[IllegalArgumentException](bd.caseOther(a, b, c, d, e, f).untyped())
    assert(caseOtherBuild3 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e, f, g))

    val iteBuild1 = bd.ite(a, b, c).untyped()

    assert(iteBuild1 == OperEx(TlaControlOper.ifThenElse, a, b, c))

    //    val letInBuild1 = bd.letIn( a, TlaOperDecl( "b" , List(), c ) )
    //    val letInBuild2 =
    //      bd.letIn(
    //        a,
    //        TlaOperDecl(
    //          "b" ,
    //          List(
    //            SimpleFormalParam( "x" ),
    //            OperFormalParam( "f", FixedArity( 0 ) )
    //          ),
    //          c
    //        )
    //      )
    //
    //    assert( letInBuild1 == OperEx( new LetInOper( List(TlaOperDecl( "b" , List(), c ) ) ), a ) )

  }

  test("Test byName: TlaControlOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val f = NameEx("f")
    val g = NameEx("g")
    val caseBuild1 = bd.byName(TlaControlOper.caseNoOther.name, a, b).untyped()
    val caseBuild2 = bd.byName(TlaControlOper.caseWithOther.name, a, b, c).untyped()
    val caseBuild3 = bd.byName(TlaControlOper.caseNoOther.name, a, b, c, d).untyped()
    val caseBuild4 = bd.byName(TlaControlOper.caseWithOther.name, a, b, c, d, e).untyped()
    val caseBuild5 = bd.byName(TlaControlOper.caseNoOther.name, a, b, c, d, e, f).untyped()
    val caseBuild6 = bd.byName(TlaControlOper.caseWithOther.name, a, b, c, d, e, f, g).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, a, b))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, a, b, c))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, a, b, c, d))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, a, b, c, d, e, f))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e, f, g))

    val caseNoOtherBuild = bd.byName(TlaControlOper.caseNoOther.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseNoOther.name).untyped())
    assert(caseNoOtherBuild == OperEx(TlaControlOper.caseNoOther, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseNoOther.name, a, b, c).untyped())

    val caseWithOtherBuild = bd.byName(TlaControlOper.caseWithOther.name, a, b, c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name, a).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name, a, b).untyped())
    assert(caseWithOtherBuild == OperEx(TlaControlOper.caseWithOther, a, b, c))

    val iteBuild = bd.byName(TlaControlOper.ifThenElse.name, a, b, c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.ifThenElse.name, a, b).untyped())
    assert(iteBuild == OperEx(TlaControlOper.ifThenElse, a, b, c))
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.ifThenElse.name, a, b, c, d).untyped())
  }

  test("Test byNameOrNull: TlaControlOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val f = NameEx("f")
    val g = NameEx("g")
    val caseBuild1 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, a, b).untyped()
    val caseBuild2 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, a, b, c).untyped()
    val caseBuild3 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, a, b, c, d).untyped()
    val caseBuild4 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, a, b, c, d, e).untyped()
    val caseBuild5 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, a, b, c, d, e, f).untyped()
    val caseBuild6 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, a, b, c, d, e, f, g).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, a, b))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, a, b, c))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, a, b, c, d))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, a, b, c, d, e, f))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, a, b, c, d, e, f, g))

    val caseNoOtherBuildEmpty = bd.byNameOrNull(TlaControlOper.caseNoOther.name).untyped()
    val caseNoOtherBuild = bd.byNameOrNull(TlaControlOper.caseNoOther.name, a, b).untyped()
    val caseNoOtherBuildBad = bd.byNameOrNull(TlaControlOper.caseNoOther.name, a, b, c).untyped()

    assert(caseNoOtherBuildEmpty == NullEx)
    assert(caseNoOtherBuild == OperEx(TlaControlOper.caseNoOther, a, b))
    assert(caseNoOtherBuildBad == NullEx)

    val caseWithOtherBuildEmpty = bd.byNameOrNull(TlaControlOper.caseWithOther.name).untyped()
    val caseWithOtherBuildSingle = bd.byNameOrNull(TlaControlOper.caseWithOther.name, a).untyped()
    val caseWithOtherBuildBad = bd.byNameOrNull(TlaControlOper.caseWithOther.name, a, b).untyped()
    val caseWithOtherBuild = bd.byNameOrNull(TlaControlOper.caseWithOther.name, a, b, c).untyped()

    assert(caseWithOtherBuildEmpty == NullEx)
    assert(caseWithOtherBuildSingle == NullEx)
    assert(caseWithOtherBuildBad == NullEx)
    assert(caseWithOtherBuild == OperEx(TlaControlOper.caseWithOther, a, b, c))

    val iteBuildBad1 = bd.byNameOrNull(TlaControlOper.ifThenElse.name, a, b).untyped()
    val iteBuild = bd.byNameOrNull(TlaControlOper.ifThenElse.name, a, b, c).untyped()
    val iteBuildBad2 = bd.byNameOrNull(TlaControlOper.ifThenElse.name, a, b, c, d).untyped()

    assert(iteBuildBad1 == NullEx)
    assert(iteBuild == OperEx(TlaControlOper.ifThenElse, a, b, c))
    assert(iteBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaTempOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val AABuild = bd.AA(a, b).untyped()

    assert(AABuild == OperEx(TlaTempOper.AA, a, b))

    val EEBuild = bd.EE(a, b).untyped()

    assert(EEBuild == OperEx(TlaTempOper.EE, a, b))

    val boxBuild = bd.box(a).untyped()

    assert(boxBuild == OperEx(TlaTempOper.box, a))

    val diamondBuild = bd.diamond(a).untyped()

    assert(diamondBuild == OperEx(TlaTempOper.diamond, a))

    val leadsToBuild = bd.leadsTo(a, b).untyped()

    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, a, b))

    val guaranteesBuild = bd.guarantees(a, b).untyped()

    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, a, b))

    val strongFairnessBuild = bd.SF(a, b).untyped()

    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, a, b))

    val weakFairnessBuild = bd.WF(a, b).untyped()

    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, a, b))
  }

  test("Test byName: TlaTempOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val AABuild = bd.byName(TlaTempOper.AA.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.AA.name, a).untyped())
    assert(AABuild == OperEx(TlaTempOper.AA, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.AA.name, a, b, c).untyped())

    val EEBuild = bd.byName(TlaTempOper.EE.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.EE.name, a).untyped())
    assert(EEBuild == OperEx(TlaTempOper.EE, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.EE.name, a, b, c).untyped())

    val boxBuild = bd.byName(TlaTempOper.box.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.box.name).untyped())
    assert(boxBuild == OperEx(TlaTempOper.box, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.box.name, a, b).untyped())

    val diamondBuild = bd.byName(TlaTempOper.diamond.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.diamond.name).untyped())
    assert(diamondBuild == OperEx(TlaTempOper.diamond, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.diamond.name, a, b).untyped())

    val leadsToBuild = bd.byName(TlaTempOper.leadsTo.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.leadsTo.name, a).untyped())
    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.leadsTo.name, a, b, c).untyped())

    val guaranteesBuild = bd.byName(TlaTempOper.guarantees.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.guarantees.name, a).untyped())
    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.guarantees.name, a, b, c).untyped())

    val strongFairnessBuild = bd.byName(TlaTempOper.strongFairness.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.strongFairness.name, a).untyped())
    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.strongFairness.name, a, b, c).untyped())

    val weakFairnessBuild = bd.byName(TlaTempOper.weakFairness.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.weakFairness.name, a).untyped())
    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.weakFairness.name, a, b, c).untyped())

  }

  test("Test byNameOrNull: TlaTempOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val AABuildBad1 = bd.byNameOrNull(TlaTempOper.AA.name, a).untyped()
    val AABuild = bd.byNameOrNull(TlaTempOper.AA.name, a, b).untyped()
    val AABuildBad2 = bd.byNameOrNull(TlaTempOper.AA.name, a, b, c).untyped()

    assert(AABuildBad1 == NullEx)
    assert(AABuild == OperEx(TlaTempOper.AA, a, b))
    assert(AABuildBad2 == NullEx)

    val EEBuildBad1 = bd.byNameOrNull(TlaTempOper.EE.name, a).untyped()
    val EEBuild = bd.byNameOrNull(TlaTempOper.EE.name, a, b).untyped()
    val EEBuildBad2 = bd.byNameOrNull(TlaTempOper.EE.name, a, b, c).untyped()

    assert(EEBuildBad1 == NullEx)
    assert(EEBuild == OperEx(TlaTempOper.EE, a, b))
    assert(EEBuildBad2 == NullEx)

    val boxBuildBad1 = bd.byNameOrNull(TlaTempOper.box.name).untyped()
    val boxBuild = bd.byNameOrNull(TlaTempOper.box.name, a).untyped()
    val boxBuildBad2 = bd.byNameOrNull(TlaTempOper.box.name, a, b).untyped()

    assert(boxBuildBad1 == NullEx)
    assert(boxBuild == OperEx(TlaTempOper.box, a))
    assert(boxBuildBad2 == NullEx)

    val diamondBuildBad1 = bd.byNameOrNull(TlaTempOper.diamond.name).untyped()
    val diamondBuild = bd.byNameOrNull(TlaTempOper.diamond.name, a).untyped()
    val diamondBuildBad2 = bd.byNameOrNull(TlaTempOper.diamond.name, a, b).untyped()

    assert(diamondBuildBad1 == NullEx)
    assert(diamondBuild == OperEx(TlaTempOper.diamond, a))
    assert(diamondBuildBad2 == NullEx)

    val leadsToBuildBad1 = bd.byNameOrNull(TlaTempOper.leadsTo.name, a).untyped()
    val leadsToBuild = bd.byNameOrNull(TlaTempOper.leadsTo.name, a, b).untyped()
    val leadsToBuildBad2 = bd.byNameOrNull(TlaTempOper.leadsTo.name, a, b, c).untyped()

    assert(leadsToBuildBad1 == NullEx)
    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, a, b))
    assert(leadsToBuildBad2 == NullEx)

    val guaranteesBuildBad1 = bd.byNameOrNull(TlaTempOper.guarantees.name, a).untyped()
    val guaranteesBuild = bd.byNameOrNull(TlaTempOper.guarantees.name, a, b).untyped()
    val guaranteesBuildBad2 = bd.byNameOrNull(TlaTempOper.guarantees.name, a, b, c).untyped()

    assert(guaranteesBuildBad1 == NullEx)
    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, a, b))
    assert(guaranteesBuildBad2 == NullEx)

    val strongFairnessBuildBad1 = bd.byNameOrNull(TlaTempOper.strongFairness.name, a).untyped()
    val strongFairnessBuild = bd.byNameOrNull(TlaTempOper.strongFairness.name, a, b).untyped()
    val strongFairnessBuildBad2 = bd.byNameOrNull(TlaTempOper.strongFairness.name, a, b, c).untyped()

    assert(strongFairnessBuildBad1 == NullEx)
    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, a, b))
    assert(strongFairnessBuildBad2 == NullEx)

    val weakFairnessBuildBad1 = bd.byNameOrNull(TlaTempOper.weakFairness.name, a).untyped()
    val weakFairnessBuild = bd.byNameOrNull(TlaTempOper.weakFairness.name, a, b).untyped()
    val weakFairnessBuildBad2 = bd.byNameOrNull(TlaTempOper.weakFairness.name, a, b, c).untyped()

    assert(weakFairnessBuildBad1 == NullEx)
    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, a, b))
    assert(weakFairnessBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaArithOper") {

    val a = NameEx("a")
    val b = NameEx("b")
    val plusBuild1 = bd.plus(a, b).untyped()
    val plusBuild2 = bd.plus(a, bd.int(2)).untyped()
    val plusBuild3 = bd.plus(bd.int(1), b).untyped()
    val plusBuild4 = bd.plus(bd.int(1), bd.int(2)).untyped()

    assert(plusBuild1 == OperEx(TlaArithOper.plus, a, b))
    assert(plusBuild2 == OperEx(TlaArithOper.plus, a, ValEx(TlaInt(2))))
    assert(plusBuild3 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), b))
    assert(plusBuild4 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val minusBuild1 = bd.minus(a, b).untyped()
    val minusBuild2 = bd.minus(a, bd.int(2)).untyped()
    val minusBuild3 = bd.minus(bd.int(1), b).untyped()
    val minusBuild4 = bd.minus(bd.int(1), bd.int(2)).untyped()

    assert(minusBuild1 == OperEx(TlaArithOper.minus, a, b))
    assert(minusBuild2 == OperEx(TlaArithOper.minus, a, ValEx(TlaInt(2))))
    assert(minusBuild3 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), b))
    assert(minusBuild4 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val uminusBuild = bd.uminus(a).untyped()

    assert(uminusBuild == OperEx(TlaArithOper.uminus, a))

    val multBuild1 = bd.mult(a, b).untyped()
    val multBuild2 = bd.mult(a, bd.int(2)).untyped()
    val multBuild3 = bd.mult(bd.int(1), b).untyped()
    val multBuild4 = bd.mult(bd.int(1), bd.int(2)).untyped()

    assert(multBuild1 == OperEx(TlaArithOper.mult, a, b))
    assert(multBuild2 == OperEx(TlaArithOper.mult, a, ValEx(TlaInt(2))))
    assert(multBuild3 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), b))
    assert(multBuild4 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val divBuild1 = bd.div(a, b).untyped()
    val divBuild2 = bd.div(a, bd.int(2)).untyped()
    val divBuild3 = bd.div(bd.int(1), b).untyped()
    val divBuild4 = bd.div(bd.int(1), bd.int(2)).untyped()

    assert(divBuild1 == OperEx(TlaArithOper.div, a, b))
    assert(divBuild2 == OperEx(TlaArithOper.div, a, ValEx(TlaInt(2))))
    assert(divBuild3 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), b))
    assert(divBuild4 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val modBuild1 = bd.mod(a, b).untyped()
    val modBuild2 = bd.mod(a, bd.int(2)).untyped()
    val modBuild3 = bd.mod(bd.int(1), b).untyped()
    val modBuild4 = bd.mod(bd.int(1), bd.int(2)).untyped()

    assert(modBuild1 == OperEx(TlaArithOper.mod, a, b))
    assert(modBuild2 == OperEx(TlaArithOper.mod, a, ValEx(TlaInt(2))))
    assert(modBuild3 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), b))
    assert(modBuild4 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val realDivBuild1 = bd.rDiv(a, b).untyped()
    val realDivBuild2 = bd.rDiv(a, bd.int(2)).untyped()
    val realDivBuild3 = bd.rDiv(bd.int(1), b).untyped()
    val realDivBuild4 = bd.rDiv(bd.int(1), bd.int(2)).untyped()

    assert(realDivBuild1 == OperEx(TlaArithOper.realDiv, a, b))
    assert(realDivBuild2 == OperEx(TlaArithOper.realDiv, a, ValEx(TlaInt(2))))
    assert(realDivBuild3 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), b))
    assert(realDivBuild4 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val expBuild1 = bd.exp(a, b).untyped()
    val expBuild2 = bd.exp(a, bd.int(2)).untyped()
    val expBuild3 = bd.exp(bd.int(1), b).untyped()
    val expBuild4 = bd.exp(bd.int(1), bd.int(2)).untyped()

    assert(expBuild1 == OperEx(TlaArithOper.exp, a, b))
    assert(expBuild2 == OperEx(TlaArithOper.exp, a, ValEx(TlaInt(2))))
    assert(expBuild3 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), b))
    assert(expBuild4 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val dotdotBuild1 = bd.dotdot(a, b).untyped()
    val dotdotBuild2 = bd.dotdot(a, bd.int(2)).untyped()
    val dotdotBuild3 = bd.dotdot(bd.int(1), b).untyped()
    val dotdotBuild4 = bd.dotdot(bd.int(1), bd.int(2)).untyped()

    assert(dotdotBuild1 == OperEx(TlaArithOper.dotdot, a, b))
    assert(dotdotBuild2 == OperEx(TlaArithOper.dotdot, a, ValEx(TlaInt(2))))
    assert(dotdotBuild3 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), b))
    assert(dotdotBuild4 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val ltBuild1 = bd.lt(a, b).untyped()
    val ltBuild2 = bd.lt(a, bd.int(2)).untyped()
    val ltBuild3 = bd.lt(bd.int(1), b).untyped()
    val ltBuild4 = bd.lt(bd.int(1), bd.int(2)).untyped()

    assert(ltBuild1 == OperEx(TlaArithOper.lt, a, b))
    assert(ltBuild2 == OperEx(TlaArithOper.lt, a, ValEx(TlaInt(2))))
    assert(ltBuild3 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), b))
    assert(ltBuild4 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val gtBuild1 = bd.gt(a, b).untyped()
    val gtBuild2 = bd.gt(a, bd.int(2)).untyped()
    val gtBuild3 = bd.gt(bd.int(1), b).untyped()
    val gtBuild4 = bd.gt(bd.int(1), bd.int(2)).untyped()

    assert(gtBuild1 == OperEx(TlaArithOper.gt, a, b))
    assert(gtBuild2 == OperEx(TlaArithOper.gt, a, ValEx(TlaInt(2))))
    assert(gtBuild3 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), b))
    assert(gtBuild4 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val leBuild1 = bd.le(a, b).untyped()
    val leBuild2 = bd.le(a, bd.int(2)).untyped()
    val leBuild3 = bd.le(bd.int(1), b).untyped()
    val leBuild4 = bd.le(bd.int(1), bd.int(2)).untyped()

    assert(leBuild1 == OperEx(TlaArithOper.le, a, b))
    assert(leBuild2 == OperEx(TlaArithOper.le, a, ValEx(TlaInt(2))))
    assert(leBuild3 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), b))
    assert(leBuild4 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val geBuild1 = bd.ge(a, b).untyped()
    val geBuild2 = bd.ge(a, bd.int(2)).untyped()
    val geBuild3 = bd.ge(bd.int(1), b).untyped()
    val geBuild4 = bd.ge(bd.int(1), bd.int(2)).untyped()

    assert(geBuild1 == OperEx(TlaArithOper.ge, a, b))
    assert(geBuild2 == OperEx(TlaArithOper.ge, a, ValEx(TlaInt(2))))
    assert(geBuild3 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), b))
    assert(geBuild4 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
  }

  test("Test byName: TlaArithOper") {

    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val plusBuild = bd.byName(TlaArithOper.plus.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, a).untyped())
    assert(plusBuild == OperEx(TlaArithOper.plus, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, a, b, c).untyped())

    val minusBuild = bd.byName(TlaArithOper.minus.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.minus.name, a).untyped())
    assert(minusBuild == OperEx(TlaArithOper.minus, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.minus.name, a, b, c).untyped())

    val uminusBuild = bd.byName(TlaArithOper.uminus.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.uminus.name).untyped())
    assert(uminusBuild == OperEx(TlaArithOper.uminus, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.uminus.name, a, b, c).untyped())

    val multBuild = bd.byName(TlaArithOper.mult.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mult.name, a).untyped())
    assert(multBuild == OperEx(TlaArithOper.mult, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mult.name, a, b, c).untyped())

    val divBuild = bd.byName(TlaArithOper.div.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.div.name, a).untyped())
    assert(divBuild == OperEx(TlaArithOper.div, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.div.name, a, b, c).untyped())

    val modBuild = bd.byName(TlaArithOper.mod.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mod.name, a).untyped())
    assert(modBuild == OperEx(TlaArithOper.mod, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mod.name, a, b, c).untyped())

    val realDivBuild = bd.byName(TlaArithOper.realDiv.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.realDiv.name, a).untyped())
    assert(realDivBuild == OperEx(TlaArithOper.realDiv, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.realDiv.name, a, b, c).untyped())

    val expBuild = bd.byName(TlaArithOper.exp.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.exp.name, a).untyped())
    assert(expBuild == OperEx(TlaArithOper.exp, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.exp.name, a, b, c).untyped())

    val dotdotBuild = bd.byName(TlaArithOper.dotdot.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.dotdot.name, a).untyped())
    assert(dotdotBuild == OperEx(TlaArithOper.dotdot, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.dotdot.name, a, b, c).untyped())

    val ltBuild = bd.byName(TlaArithOper.lt.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.lt.name, a).untyped())
    assert(ltBuild == OperEx(TlaArithOper.lt, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.lt.name, a, b, c).untyped())

    val gtBuild = bd.byName(TlaArithOper.gt.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.gt.name, a).untyped())
    assert(gtBuild == OperEx(TlaArithOper.gt, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.gt.name, a, b, c).untyped())

    val leBuild = bd.byName(TlaArithOper.le.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.le.name, a).untyped())
    assert(leBuild == OperEx(TlaArithOper.le, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.le.name, a, b, c).untyped())

    val geBuild = bd.byName(TlaArithOper.ge.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.ge.name, a).untyped())
    assert(geBuild == OperEx(TlaArithOper.ge, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.ge.name, a, b, c).untyped())
  }

  test("Test byNameOrNull: TlaArithOper") {

    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val plusBuildBad1 = bd.byNameOrNull(TlaArithOper.plus.name, a).untyped()
    val plusBuild = bd.byNameOrNull(TlaArithOper.plus.name, a, b).untyped()
    val plusBuildBad2 = bd.byNameOrNull(TlaArithOper.plus.name, a, b, c).untyped()

    assert(plusBuildBad1 == NullEx)
    assert(plusBuild == OperEx(TlaArithOper.plus, a, b))
    assert(plusBuildBad2 == NullEx)

    val minusBuildBad1 = bd.byNameOrNull(TlaArithOper.minus.name, a).untyped()
    val minusBuild = bd.byNameOrNull(TlaArithOper.minus.name, a, b).untyped()
    val minusBuildBad2 = bd.byNameOrNull(TlaArithOper.minus.name, a, b, c).untyped()

    assert(minusBuildBad1 == NullEx)
    assert(minusBuild == OperEx(TlaArithOper.minus, a, b))
    assert(minusBuildBad2 == NullEx)

    val uminusBuildBad1 = bd.byNameOrNull(TlaArithOper.uminus.name).untyped()
    val uminusBuild = bd.byNameOrNull(TlaArithOper.uminus.name, a).untyped()
    val uminusBuildBad2 = bd.byNameOrNull(TlaArithOper.uminus.name, a, b, c).untyped()

    assert(uminusBuildBad1 == NullEx)
    assert(uminusBuild == OperEx(TlaArithOper.uminus, a))
    assert(uminusBuildBad2 == NullEx)

    val multBuildBad1 = bd.byNameOrNull(TlaArithOper.mult.name, a).untyped()
    val multBuild = bd.byNameOrNull(TlaArithOper.mult.name, a, b).untyped()
    val multBuildBad2 = bd.byNameOrNull(TlaArithOper.mult.name, a, b, c).untyped()

    assert(multBuildBad1 == NullEx)
    assert(multBuild == OperEx(TlaArithOper.mult, a, b))
    assert(multBuildBad2 == NullEx)

    val divBuildBad1 = bd.byNameOrNull(TlaArithOper.div.name, a).untyped()
    val divBuild = bd.byNameOrNull(TlaArithOper.div.name, a, b).untyped()
    val divBuildBad2 = bd.byNameOrNull(TlaArithOper.div.name, a, b, c).untyped()

    assert(divBuildBad1 == NullEx)
    assert(divBuild == OperEx(TlaArithOper.div, a, b))
    assert(divBuildBad2 == NullEx)

    val modBuildBad1 = bd.byNameOrNull(TlaArithOper.mod.name, a).untyped()
    val modBuild = bd.byNameOrNull(TlaArithOper.mod.name, a, b).untyped()
    val modBuildBad2 = bd.byNameOrNull(TlaArithOper.mod.name, a, b, c).untyped()

    assert(modBuildBad1 == NullEx)
    assert(modBuild == OperEx(TlaArithOper.mod, a, b))
    assert(modBuildBad2 == NullEx)

    val realDivBuildBad1 = bd.byNameOrNull(TlaArithOper.realDiv.name, a).untyped()
    val realDivBuild = bd.byNameOrNull(TlaArithOper.realDiv.name, a, b).untyped()
    val realDivBuildBad2 = bd.byNameOrNull(TlaArithOper.realDiv.name, a, b, c).untyped()

    assert(realDivBuildBad1 == NullEx)
    assert(realDivBuild == OperEx(TlaArithOper.realDiv, a, b))
    assert(realDivBuildBad2 == NullEx)

    val expBuildBad1 = bd.byNameOrNull(TlaArithOper.exp.name, a).untyped()
    val expBuild = bd.byNameOrNull(TlaArithOper.exp.name, a, b).untyped()
    val expBuildBad2 = bd.byNameOrNull(TlaArithOper.exp.name, a, b, c).untyped()

    assert(expBuildBad1 == NullEx)
    assert(expBuild == OperEx(TlaArithOper.exp, a, b))
    assert(expBuildBad2 == NullEx)

    val dotdotBuildBad1 = bd.byNameOrNull(TlaArithOper.dotdot.name, a).untyped()
    val dotdotBuild = bd.byNameOrNull(TlaArithOper.dotdot.name, a, b).untyped()
    val dotdotBuildBad2 = bd.byNameOrNull(TlaArithOper.dotdot.name, a, b, c).untyped()

    assert(dotdotBuildBad1 == NullEx)
    assert(dotdotBuild == OperEx(TlaArithOper.dotdot, a, b))
    assert(dotdotBuildBad2 == NullEx)

    val ltBuildBad1 = bd.byNameOrNull(TlaArithOper.lt.name, a).untyped()
    val ltBuild = bd.byNameOrNull(TlaArithOper.lt.name, a, b).untyped()
    val ltBuildBad2 = bd.byNameOrNull(TlaArithOper.lt.name, a, b, c).untyped()

    assert(ltBuildBad1 == NullEx)
    assert(ltBuild == OperEx(TlaArithOper.lt, a, b))
    assert(ltBuildBad2 == NullEx)

    val gtBuildBad1 = bd.byNameOrNull(TlaArithOper.gt.name, a).untyped()
    val gtBuild = bd.byNameOrNull(TlaArithOper.gt.name, a, b).untyped()
    val gtBuildBad2 = bd.byNameOrNull(TlaArithOper.gt.name, a, b, c).untyped()

    assert(gtBuildBad1 == NullEx)
    assert(gtBuild == OperEx(TlaArithOper.gt, a, b))
    assert(gtBuildBad2 == NullEx)

    val leBuildBad1 = bd.byNameOrNull(TlaArithOper.le.name, a).untyped()
    val leBuild = bd.byNameOrNull(TlaArithOper.le.name, a, b).untyped()
    val leBuildBad2 = bd.byNameOrNull(TlaArithOper.le.name, a, b, c).untyped()

    assert(leBuildBad1 == NullEx)
    assert(leBuild == OperEx(TlaArithOper.le, a, b))
    assert(leBuildBad2 == NullEx)

    val geBuildBad1 = bd.byNameOrNull(TlaArithOper.ge.name, a).untyped()
    val geBuild = bd.byNameOrNull(TlaArithOper.ge.name, a, b).untyped()
    val geBuildBad2 = bd.byNameOrNull(TlaArithOper.ge.name, a, b, c).untyped()

    assert(geBuildBad1 == NullEx)
    assert(geBuild == OperEx(TlaArithOper.ge, a, b))
    assert(geBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaFiniteSetOper") {
    val a = NameEx("a")
    val cardinalityBuild = bd.card(a).untyped()

    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, a))

    val isFiniteSetBuild = bd.isFin(a).untyped()

    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, a))
  }

  test("Test byName: TlaFiniteSetOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val cardinalityBuild = bd.byName(TlaFiniteSetOper.cardinality.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.cardinality.name).untyped())
    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.cardinality.name, a, b, c).untyped())

    val isFiniteSetBuild = bd.byName(TlaFiniteSetOper.isFiniteSet.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.isFiniteSet.name).untyped())
    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.isFiniteSet.name, a, b, c).untyped())
  }

  test("Test byNameOrNull: TlaFiniteSetOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val cardinalityBuildBad1 = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name).untyped()
    val cardinalityBuild = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name, a).untyped()
    val cardinalityBuildBad2 = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name, a, b, c).untyped()

    assert(cardinalityBuildBad1 == NullEx)
    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, a))
    assert(cardinalityBuildBad2 == NullEx)

    val isFiniteSetBuildBad1 = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name).untyped()
    val isFiniteSetBuild = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name, a).untyped()
    val isFiniteSetBuildBad2 = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name, a, b, c).untyped()

    assert(isFiniteSetBuildBad1 == NullEx)
    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, a))
    assert(isFiniteSetBuildBad2 == NullEx)

  }

  test("Test direct methods: TlaFunOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val f = NameEx("f")
    val appBuild = bd.appFun(a, b).untyped()

    assert(appBuild == OperEx(TlaFunOper.app, a, b))

    val domainBuild = bd.dom(a).untyped()

    assert(domainBuild == OperEx(TlaFunOper.domain, a))

    val enumBuild1 = bd.enumFun(a, b).untyped()
    val enumBuild2 = bd.enumFun(a, b, c, d).untyped()

    assert(enumBuild1 == OperEx(TlaFunOper.rec, a, b))
    assertThrows[IllegalArgumentException](bd.enumFun(a, b, c).untyped())
    assert(enumBuild2 == OperEx(TlaFunOper.rec, a, b, c, d))
    assertThrows[IllegalArgumentException](bd.enumFun(a, b, c, d, e).untyped())

    val exceptBuild1 = bd.except(a, b, c).untyped()
    val exceptBuild2 = bd.except(a, b, c, d, e).untyped()

    assert(exceptBuild1 == OperEx(TlaFunOper.except, a, b, c))
    assertThrows[IllegalArgumentException](bd.except(a, b, c, d).untyped())
    assert(exceptBuild2 == OperEx(TlaFunOper.except, a, b, c, d, e))
    assertThrows[IllegalArgumentException](bd.except(a, b, c, d, e, f).untyped())

    val funDefBuild1 = bd.funDef(a, b, c).untyped()
    val funDefBuild2 = bd.funDef(a, b, c, d, e).untyped()

    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, a, b, c))
    assertThrows[IllegalArgumentException](bd.funDef(a, b, c, d).untyped())
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, a, b, c, d, e))
    assertThrows[IllegalArgumentException](bd.funDef(a, b, c, d, e, f).untyped())

    val tupleBuild1 = bd.tuple().untyped()
    val tupleBuild2 = bd.tuple(a, b).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, a, b))
  }

  test("Test byName: TlaFunOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val f = NameEx("f")
    val appBuild = bd.byName(TlaFunOper.app.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.app.name, a).untyped())
    assert(appBuild == OperEx(TlaFunOper.app, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.app.name, a, b, c).untyped())

    val domainBuild = bd.byName(TlaFunOper.domain.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.domain.name).untyped())
    assert(domainBuild == OperEx(TlaFunOper.domain, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.domain.name, a, b, c).untyped())

    val enumBuild1 = bd.byName(TlaFunOper.rec.name, a, b).untyped()
    val enumBuild2 = bd.byName(TlaFunOper.rec.name, a, b, c, d).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.rec.name, a).untyped())
    assert(enumBuild1 == OperEx(TlaFunOper.rec, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.rec.name, a, b, c).untyped())
    assert(enumBuild2 == OperEx(TlaFunOper.rec, a, b, c, d))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.rec.name, a, b, c, d, e).untyped())

    val exceptBuild1 = bd.byName(TlaFunOper.except.name, a, b, c).untyped()
    val exceptBuild2 = bd.byName(TlaFunOper.except.name, a, b, c, d, e).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, a).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, a, b).untyped())
    assert(exceptBuild1 == OperEx(TlaFunOper.except, a, b, c))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, a, b, c, d).untyped())
    assert(exceptBuild2 == OperEx(TlaFunOper.except, a, b, c, d, e))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, a, b, c, d, e, f).untyped())

    val funDefBuild1 = bd.byName(TlaFunOper.funDef.name, a, b, c).untyped()
    val funDefBuild2 = bd.byName(TlaFunOper.funDef.name, a, b, c, d, e).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, a).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, a, b).untyped())
    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, a, b, c))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, a, b, c, d).untyped())
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, a, b, c, d, e))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, a, b, c, d, e, f).untyped())

    val tupleBuild1 = bd.byName(TlaFunOper.tuple.name).untyped()
    val tupleBuild2 = bd.byName(TlaFunOper.tuple.name, a, b).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, a, b))

  }

  test("Test byNameOrNull: TlaFunOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val appBuildBad1 = bd.byNameOrNull(TlaFunOper.app.name, a).untyped()
    val appBuild = bd.byNameOrNull(TlaFunOper.app.name, a, b).untyped()
    val appBuildBad2 = bd.byNameOrNull(TlaFunOper.app.name, a, b, c).untyped()

    assert(appBuildBad1 == NullEx)
    assert(appBuild == OperEx(TlaFunOper.app, a, b))
    assert(appBuildBad2 == NullEx)

    val domainBuildBad1 = bd.byNameOrNull(TlaFunOper.domain.name).untyped()
    val domainBuild = bd.byNameOrNull(TlaFunOper.domain.name, a).untyped()
    val domainBuildBad2 = bd.byNameOrNull(TlaFunOper.domain.name, a, b, c).untyped()

    assert(domainBuildBad1 == NullEx)
    assert(domainBuild == OperEx(TlaFunOper.domain, a))
    assert(domainBuildBad2 == NullEx)

    val enumBuildEmpty = bd.byNameOrNull(TlaFunOper.rec.name).untyped()
    val enumBuild1 = bd.byNameOrNull(TlaFunOper.rec.name, a, b).untyped()
    val enumBuildBad1 = bd.byNameOrNull(TlaFunOper.rec.name, a, b, c).untyped()
    val enumBuild2 = bd.byNameOrNull(TlaFunOper.rec.name, a, b, c, d).untyped()
    val enumBuildBad2 = bd.byNameOrNull(TlaFunOper.rec.name, a, b, c, d, e).untyped()

    assert(enumBuildEmpty == OperEx(TlaFunOper.rec))
    assert(enumBuild1 == OperEx(TlaFunOper.rec, a, b))
    assert(enumBuildBad1 == NullEx)
    assert(enumBuild2 == OperEx(TlaFunOper.rec, a, b, c, d))
    assert(enumBuildBad2 == NullEx)

    val exceptBuildEmpty = bd.byNameOrNull(TlaFunOper.except.name).untyped()
    val exceptBuildSingle = bd.byNameOrNull(TlaFunOper.except.name, a).untyped()
    val exceptBuildBad1 = bd.byNameOrNull(TlaFunOper.except.name, a, b).untyped()
    val exceptBuild1 = bd.byNameOrNull(TlaFunOper.except.name, a, b, c).untyped()
    val exceptBuildBad2 = bd.byNameOrNull(TlaFunOper.except.name, a, b, c, d).untyped()
    val exceptBuild2 = bd.byNameOrNull(TlaFunOper.except.name, a, b, c, d, e).untyped()

    assert(exceptBuildEmpty == NullEx)
    assert(exceptBuildSingle == NullEx)
    assert(exceptBuildBad1 == NullEx)
    assert(exceptBuild1 == OperEx(TlaFunOper.except, a, b, c))
    assert(exceptBuildBad2 == NullEx)
    assert(exceptBuild2 == OperEx(TlaFunOper.except, a, b, c, d, e))

    val funDefBuildEmpty = bd.byNameOrNull(TlaFunOper.funDef.name).untyped()
    val funDefBuildSingle = bd.byNameOrNull(TlaFunOper.funDef.name, a).untyped()
    val funDefBuildBad1 = bd.byNameOrNull(TlaFunOper.funDef.name, a, b).untyped()
    val funDefBuild1 = bd.byNameOrNull(TlaFunOper.funDef.name, a, b, c).untyped()
    val funDefBuildBad2 = bd.byNameOrNull(TlaFunOper.funDef.name, a, b, c, d).untyped()
    val funDefBuild2 = bd.byNameOrNull(TlaFunOper.funDef.name, a, b, c, d, e).untyped()

    assert(funDefBuildEmpty == NullEx)
    assert(funDefBuildSingle == NullEx)
    assert(funDefBuildBad1 == NullEx)
    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, a, b, c))
    assert(funDefBuildBad2 == NullEx)
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, a, b, c, d, e))

    val tupleBuild1 = bd.byNameOrNull(TlaFunOper.tuple.name).untyped()
    val tupleBuild2 = bd.byNameOrNull(TlaFunOper.tuple.name, a, b).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, a, b))
  }

  test("Test direct methods: TlaSeqOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val appendBuild = bd.append(a, b).untyped()

    assert(appendBuild == OperEx(TlaSeqOper.append, a, b))

    val concatBuild = bd.concat(a, b).untyped()

    assert(concatBuild == OperEx(TlaSeqOper.concat, a, b))

    val headBuild = bd.head(a).untyped()

    assert(headBuild == OperEx(TlaSeqOper.head, a))

    val tailBuild = bd.tail(a).untyped()

    assert(tailBuild == OperEx(TlaSeqOper.tail, a))

    val lenBuild = bd.len(a).untyped()

    assert(lenBuild == OperEx(TlaSeqOper.len, a))
  }

  test("Test byName: TlaSeqOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val appendBuild = bd.byName(TlaSeqOper.append.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.append.name, a).untyped())
    assert(appendBuild == OperEx(TlaSeqOper.append, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.append.name, a, b, c).untyped())

    val concatBuild = bd.byName(TlaSeqOper.concat.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.concat.name, a).untyped())
    assert(concatBuild == OperEx(TlaSeqOper.concat, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.concat.name, a, b, c).untyped())

    val headBuild = bd.byName(TlaSeqOper.head.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.head.name).untyped())
    assert(headBuild == OperEx(TlaSeqOper.head, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.head.name, a, b).untyped())

    val tailBuild = bd.byName(TlaSeqOper.tail.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.tail.name).untyped())
    assert(tailBuild == OperEx(TlaSeqOper.tail, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.tail.name, a, b).untyped())

    val lenBuild = bd.byName(TlaSeqOper.len.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.len.name).untyped())
    assert(lenBuild == OperEx(TlaSeqOper.len, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.len.name, a, b).untyped())
  }

  test("Test byNameOrNull: TlaSeqOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val appendBuildBad1 = bd.byNameOrNull(TlaSeqOper.append.name, a).untyped()
    val appendBuild = bd.byNameOrNull(TlaSeqOper.append.name, a, b).untyped()
    val appendBuildBad2 = bd.byNameOrNull(TlaSeqOper.append.name, a, b, c).untyped()

    assert(appendBuildBad1 == NullEx)
    assert(appendBuild == OperEx(TlaSeqOper.append, a, b))
    assert(appendBuildBad2 == NullEx)

    val concatBuildBad1 = bd.byNameOrNull(TlaSeqOper.concat.name, a).untyped()
    val concatBuild = bd.byNameOrNull(TlaSeqOper.concat.name, a, b).untyped()
    val concatBuildBad2 = bd.byNameOrNull(TlaSeqOper.concat.name, a, b, c).untyped()

    assert(concatBuildBad1 == NullEx)
    assert(concatBuild == OperEx(TlaSeqOper.concat, a, b))
    assert(concatBuildBad2 == NullEx)

    val headBuildBad1 = bd.byNameOrNull(TlaSeqOper.head.name).untyped()
    val headBuild = bd.byNameOrNull(TlaSeqOper.head.name, a).untyped()
    val headBuildBad2 = bd.byNameOrNull(TlaSeqOper.head.name, a, b).untyped()

    assert(headBuildBad1 == NullEx)
    assert(headBuild == OperEx(TlaSeqOper.head, a))
    assert(headBuildBad2 == NullEx)

    val tailBuildBad1 = bd.byNameOrNull(TlaSeqOper.tail.name).untyped()
    val tailBuild = bd.byNameOrNull(TlaSeqOper.tail.name, a).untyped()
    val tailBuildBad2 = bd.byNameOrNull(TlaSeqOper.tail.name, a, b).untyped()

    assert(tailBuildBad1 == NullEx)
    assert(tailBuild == OperEx(TlaSeqOper.tail, a))
    assert(tailBuildBad2 == NullEx)

    val lenBuildBad1 = bd.byNameOrNull(TlaSeqOper.len.name).untyped()
    val lenBuild = bd.byNameOrNull(TlaSeqOper.len.name, a).untyped()
    val lenBuildBad2 = bd.byNameOrNull(TlaSeqOper.len.name, a, b).untyped()

    assert(lenBuildBad1 == NullEx)
    assert(lenBuild == OperEx(TlaSeqOper.len, a))
    assert(lenBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaSetOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val f = NameEx("f")
    val enumSetBuild1 = bd.enumSet().untyped()
    val enumSetBuild2 = bd.enumSet(a, b).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, a, b))

    val inBuild = bd.in(a, b).untyped()

    assert(inBuild == OperEx(TlaSetOper.in, a, b))

    val notinBuild = bd.notin(a, b).untyped()

    assert(notinBuild == OperEx(TlaSetOper.notin, a, b))

    val capBuild = bd.cap(a, b).untyped()

    assert(capBuild == OperEx(TlaSetOper.cap, a, b))

    val cupBuild = bd.cup(a, b).untyped()

    assert(cupBuild == OperEx(TlaSetOper.cup, a, b))

    val unionBuild = bd.union(a).untyped()

    assert(unionBuild == OperEx(TlaSetOper.union, a))

    val filterBuild = bd.filter(a, b, c).untyped()

    assert(filterBuild == OperEx(TlaSetOper.filter, a, b, c))

    val mapBuild1 = bd.map(a, b, c).untyped()
    val mapBuild2 = bd.map(a, b, c, d, e).untyped()

    assert(mapBuild1 == OperEx(TlaSetOper.map, a, b, c))
    assertThrows[IllegalArgumentException](bd.map(a, b, c, d).untyped())
    assert(mapBuild2 == OperEx(TlaSetOper.map, a, b, c, d, e))
    assertThrows[IllegalArgumentException](bd.map(a, b, c, d, e, f).untyped())

    val funSetBuild = bd.funSet(a, b).untyped()

    assert(funSetBuild == OperEx(TlaSetOper.funSet, a, b))

    val recSetBuild1 = bd.recSet(a, b).untyped()
    val recSetBuild2 = bd.recSet(a, b, c, d).untyped()

    assert(recSetBuild1 == OperEx(TlaSetOper.recSet, a, b))
    assertThrows[IllegalArgumentException](bd.recSet(a, b, c).untyped())
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, a, b, c, d))
    assertThrows[IllegalArgumentException](bd.recSet(a, b, c, d, e).untyped())

    val seqSetBuild = bd.seqSet(a).untyped()

    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, a))

    val subseteqBuild = bd.subseteq(a, b).untyped()
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, a, b))

    val setminusBuild = bd.setminus(a, b).untyped()

    assert(setminusBuild == OperEx(TlaSetOper.setminus, a, b))

    val timesBuild1 = bd.times(a, b).untyped()
    val timesBuild2 = bd.times(a, b, c).untyped()

    assertThrows[IllegalArgumentException](bd.times().untyped())
    assertThrows[IllegalArgumentException](bd.times(a).untyped())
    assert(timesBuild1 == OperEx(TlaSetOper.times, a, b))
    assert(timesBuild2 == OperEx(TlaSetOper.times, a, b, c))

    val powSetBuild = bd.powSet(a).untyped()

    assert(powSetBuild == OperEx(TlaSetOper.powerset, a))
  }

  test("Test byName: TlaSetOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val enumSetBuild1 = bd.byName(TlaSetOper.enumSet.name).untyped()
    val enumSetBuild2 = bd.byName(TlaSetOper.enumSet.name, a, b).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, a, b))

    val inBuild = bd.byName(TlaSetOper.in.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.in.name, a).untyped())
    assert(inBuild == OperEx(TlaSetOper.in, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.in.name, a, b, c).untyped())

    val notinBuild = bd.byName(TlaSetOper.notin.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.notin.name, a).untyped())
    assert(notinBuild == OperEx(TlaSetOper.notin, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.notin.name, a, b, c).untyped())

    val capBuild = bd.byName(TlaSetOper.cap.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cap.name, a).untyped())
    assert(capBuild == OperEx(TlaSetOper.cap, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cap.name, a, b, c).untyped())

    val cupBuild = bd.byName(TlaSetOper.cup.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cup.name, a).untyped())
    assert(cupBuild == OperEx(TlaSetOper.cup, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cup.name, a, b, c).untyped())

    val unionBuild = bd.byName(TlaSetOper.union.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.union.name).untyped())
    assert(unionBuild == OperEx(TlaSetOper.union, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.union.name, a, b).untyped())

    val filterBuild = bd.byName(TlaSetOper.filter.name, a, b, c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.filter.name, a, b).untyped())
    assert(filterBuild == OperEx(TlaSetOper.filter, a, b, c))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.filter.name, a, b, c, d).untyped())

    val mapBuild1 = bd.byNameOrNull(TlaSetOper.map.name, a, b, c).untyped()
    val mapBuild2 = bd.byNameOrNull(TlaSetOper.map.name, a, b, c, d, e).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.map.name, a, b).untyped())
    assert(mapBuild1 == OperEx(TlaSetOper.map, a, b, c))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.map.name, a, b, c, d).untyped())
    assert(mapBuild2 == OperEx(TlaSetOper.map, a, b, c, d, e))

    val funSetBuild = bd.byName(TlaSetOper.funSet.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.funSet.name, a).untyped())
    assert(funSetBuild == OperEx(TlaSetOper.funSet, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.funSet.name, a, b, c).untyped())

    val recSetBuild1 = bd.byNameOrNull(TlaSetOper.recSet.name, a, b).untyped()
    val recSetBuild2 = bd.byNameOrNull(TlaSetOper.recSet.name, a, b, c, d).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, a).untyped())
    assert(recSetBuild1 == OperEx(TlaSetOper.recSet, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, a, b, c).untyped())
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, a, b, c, d))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, a, b, c, d, e).untyped())

    val seqSetBuild = bd.byName(TlaSetOper.seqSet.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.seqSet.name).untyped())
    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.seqSet.name, a, b).untyped())

    val subseteqBuild = bd.byName(TlaSetOper.subseteq.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.subseteq.name, a).untyped())
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.subseteq.name, a, b, c).untyped())

    val setminusBuild = bd.byName(TlaSetOper.setminus.name, a, b).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.setminus.name, a).untyped())
    assert(setminusBuild == OperEx(TlaSetOper.setminus, a, b))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.setminus.name, a, b, c).untyped())

    val timesBuild1 = bd.byName(TlaSetOper.times.name, a, b).untyped()
    val timesBuild2 = bd.byName(TlaSetOper.times.name, a, b, c).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.times.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.times.name, a).untyped())
    assert(timesBuild1 == OperEx(TlaSetOper.times, a, b))
    assert(timesBuild2 == OperEx(TlaSetOper.times, a, b, c))

    val powSetBuild = bd.byName(TlaSetOper.powerset.name, a).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.powerset.name).untyped())
    assert(powSetBuild == OperEx(TlaSetOper.powerset, a))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.powerset.name, a, b).untyped())

  }

  test("Test byNameOrNull: TlaSetOper") {
    val a = NameEx("a")
    val b = NameEx("b")
    val c = NameEx("c")
    val d = NameEx("d")
    val e = NameEx("e")
    val enumSetBuild1 = bd.byNameOrNull(TlaSetOper.enumSet.name).untyped()
    val enumSetBuild2 = bd.byNameOrNull(TlaSetOper.enumSet.name, a, b).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, a, b))

    val inBuildBad1 = bd.byNameOrNull(TlaSetOper.in.name, a).untyped()
    val inBuild = bd.byNameOrNull(TlaSetOper.in.name, a, b).untyped()
    val inBuildBad2 = bd.byNameOrNull(TlaSetOper.in.name, a, b, c).untyped()

    assert(inBuildBad1 == NullEx)
    assert(inBuild == OperEx(TlaSetOper.in, a, b))
    assert(inBuildBad2 == NullEx)

    val notinBuildBad1 = bd.byNameOrNull(TlaSetOper.notin.name, a).untyped()
    val notinBuild = bd.byNameOrNull(TlaSetOper.notin.name, a, b).untyped()
    val notinBuildBad2 = bd.byNameOrNull(TlaSetOper.notin.name, a, b, c).untyped()

    assert(notinBuildBad1 == NullEx)
    assert(notinBuild == OperEx(TlaSetOper.notin, a, b))
    assert(notinBuildBad2 == NullEx)

    val capBuildBad1 = bd.byNameOrNull(TlaSetOper.cap.name, a).untyped()
    val capBuild = bd.byNameOrNull(TlaSetOper.cap.name, a, b).untyped()
    val capBuildBad2 = bd.byNameOrNull(TlaSetOper.cap.name, a, b, c).untyped()

    assert(capBuildBad1 == NullEx)
    assert(capBuild == OperEx(TlaSetOper.cap, a, b))
    assert(capBuildBad2 == NullEx)

    val cupBuildBad1 = bd.byNameOrNull(TlaSetOper.cup.name, a).untyped()
    val cupBuild = bd.byNameOrNull(TlaSetOper.cup.name, a, b).untyped()
    val cupBuildBad2 = bd.byNameOrNull(TlaSetOper.cup.name, a, b, c).untyped()

    assert(cupBuildBad1 == NullEx)
    assert(cupBuild == OperEx(TlaSetOper.cup, a, b))
    assert(cupBuildBad2 == NullEx)

    val unionBuildBad1 = bd.byNameOrNull(TlaSetOper.union.name).untyped()
    val unionBuild = bd.byNameOrNull(TlaSetOper.union.name, a).untyped()
    val unionBuildBad2 = bd.byNameOrNull(TlaSetOper.union.name, a, b).untyped()

    assert(unionBuildBad1 == NullEx)
    assert(unionBuild == OperEx(TlaSetOper.union, a))
    assert(unionBuildBad2 == NullEx)

    val filterBuildBad1 = bd.byNameOrNull(TlaSetOper.filter.name, a, b).untyped()
    val filterBuild = bd.byNameOrNull(TlaSetOper.filter.name, a, b, c).untyped()
    val filterBuildBad2 = bd.byNameOrNull(TlaSetOper.filter.name, a, b, c, d).untyped()

    assert(filterBuildBad1 == NullEx)
    assert(filterBuild == OperEx(TlaSetOper.filter, a, b, c))
    assert(filterBuildBad2 == NullEx)

    val mapBuildBad1 = bd.byNameOrNull(TlaSetOper.map.name, a, b).untyped()
    val mapBuild1 = bd.byNameOrNull(TlaSetOper.map.name, a, b, c).untyped()
    val mapBuildBad2 = bd.byNameOrNull(TlaSetOper.map.name, a, b, c, d).untyped()
    val mapBuild2 = bd.byNameOrNull(TlaSetOper.map.name, a, b, c, d, e).untyped()

    assert(mapBuildBad1 == NullEx)
    assert(mapBuild1 == OperEx(TlaSetOper.map, a, b, c))
    assert(mapBuildBad2 == NullEx)
    assert(mapBuild2 == OperEx(TlaSetOper.map, a, b, c, d, e))

    val funSetBuildBad1 = bd.byNameOrNull(TlaSetOper.funSet.name, a).untyped()
    val funSetBuild = bd.byNameOrNull(TlaSetOper.funSet.name, a, b).untyped()
    val funSetBuildBad2 = bd.byNameOrNull(TlaSetOper.funSet.name, a, b, c).untyped()

    assert(funSetBuildBad1 == NullEx)
    assert(funSetBuild == OperEx(TlaSetOper.funSet, a, b))
    assert(funSetBuildBad2 == NullEx)

    val recSetBuildBad0 = bd.byNameOrNull(TlaSetOper.recSet.name).untyped()
    val recSetBuildBad1 = bd.byNameOrNull(TlaSetOper.recSet.name, a).untyped()
    val recSetBuild1 = bd.byNameOrNull(TlaSetOper.recSet.name, a, b).untyped()
    val recSetBuildBad2 = bd.byNameOrNull(TlaSetOper.recSet.name, a, b, c).untyped()
    val recSetBuild2 = bd.byNameOrNull(TlaSetOper.recSet.name, a, b, c, d).untyped()
    val recSetBuildBad3 = bd.byNameOrNull(TlaSetOper.recSet.name, a, b, c, d, e).untyped()

    assert(recSetBuildBad0 == NullEx)
    assert(recSetBuildBad1 == NullEx)
    assert(recSetBuild1 == OperEx(TlaSetOper.recSet, a, b))
    assert(recSetBuildBad2 == NullEx)
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, a, b, c, d))
    assert(recSetBuildBad3 == NullEx)

    val seqSetBuildBad1 = bd.byNameOrNull(TlaSetOper.seqSet.name).untyped()
    val seqSetBuild = bd.byNameOrNull(TlaSetOper.seqSet.name, a).untyped()
    val seqSetBuildBad2 = bd.byNameOrNull(TlaSetOper.seqSet.name, a, b).untyped()

    assert(seqSetBuildBad1 == NullEx)
    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, a))
    assert(seqSetBuildBad2 == NullEx)

    val subseteqBuildBad1 = bd.byNameOrNull(TlaSetOper.subseteq.name, a).untyped()
    val subseteqBuild = bd.byNameOrNull(TlaSetOper.subseteq.name, a, b).untyped()
    val subseteqBuildBad2 = bd.byNameOrNull(TlaSetOper.subseteq.name, a, b, c).untyped()

    assert(subseteqBuildBad1 == NullEx)
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, a, b))
    assert(subseteqBuildBad2 == NullEx)

    val setminusBuildBad1 = bd.byNameOrNull(TlaSetOper.setminus.name, a).untyped()
    val setminusBuild = bd.byNameOrNull(TlaSetOper.setminus.name, a, b).untyped()
    val setminusBuildBad2 = bd.byNameOrNull(TlaSetOper.setminus.name, a, b, c).untyped()

    assert(setminusBuildBad1 == NullEx)
    assert(setminusBuild == OperEx(TlaSetOper.setminus, a, b))
    assert(setminusBuildBad2 == NullEx)

    val timesBuildBad1 = bd.byNameOrNull(TlaSetOper.times.name).untyped()
    val timesBuildBad2 = bd.byNameOrNull(TlaSetOper.times.name, a).untyped()
    val timesBuild1 = bd.byNameOrNull(TlaSetOper.times.name, a, b).untyped()
    val timesBuild2 = bd.byNameOrNull(TlaSetOper.times.name, a, b, c).untyped()

    assert(timesBuildBad1 == NullEx)
    assert(timesBuildBad2 == NullEx)
    assert(timesBuild1 == OperEx(TlaSetOper.times, a, b))
    assert(timesBuild2 == OperEx(TlaSetOper.times, a, b, c))

    val powersetBuildBad1 = bd.byNameOrNull(TlaSetOper.powerset.name).untyped()
    val powersetBuild = bd.byNameOrNull(TlaSetOper.powerset.name, a).untyped()
    val powersetBuildBad2 = bd.byNameOrNull(TlaSetOper.powerset.name, a, b).untyped()

    assert(powersetBuildBad1 == NullEx)
    assert(powersetBuild == OperEx(TlaSetOper.powerset, a))
    assert(powersetBuildBad2 == NullEx)

  }
}

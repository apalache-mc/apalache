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
    val decl1 = bd.declOp("A", tla.name("c")).untypedOperDecl()
    val decl2 = bd.declOp("A", tla.name("x"), OperParam("x")).untypedOperDecl()
    val decl3 = bd.declOp("A", bd.appOp(tla.name("B")), OperParam("B", 0)).untypedOperDecl()
    val decl4 = bd.declOp("A", bd.appOp(tla.name("B"), tla.name("x")), OperParam("x"), OperParam("B", 1)).untypedOperDecl()

    assert(decl1 == TlaOperDecl("A", List(), tla.name("c")))
    assert(decl2 == TlaOperDecl("A", List(OperParam("x")), tla.name("x")))
    assert(decl3 ==
      TlaOperDecl(
          "A",
          List(OperParam("B", 0)),
          OperEx(TlaOper.apply, tla.name("B")),
      ))
    assert(decl4 ==
      TlaOperDecl(
          "A",
          List(OperParam("x"), OperParam("B", 1)),
          OperEx(TlaOper.apply, tla.name("B"), tla.name("x")),
      ))

    val appEx1 = bd.appDecl(decl1).untyped()
    val appEx2 = bd.appDecl(decl2, tla.name("a")).untyped()
    val appEx3 = bd.appDecl(decl3, tla.name("a")).untyped()
    val appEx4 = bd.appDecl(decl4, tla.name("a"), tla.name("b")).untyped()

    assert(appEx1 == OperEx(TlaOper.apply, tla.name(decl1.name)))
    assertThrows[IllegalArgumentException](bd.appDecl(decl1, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.appDecl(decl2))
    assert(appEx2 == OperEx(TlaOper.apply, tla.name(decl2.name), tla.name("a")))
    assertThrows[IllegalArgumentException](bd.appDecl(decl2, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.appDecl(decl3))
    assert(appEx3 == OperEx(TlaOper.apply, tla.name(decl3.name), tla.name("a")))
    assertThrows[IllegalArgumentException](bd.appDecl(decl3, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4, tla.name("a")))
    assert(appEx4 == OperEx(TlaOper.apply, tla.name(decl4.name), tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.appDecl(decl4, tla.name("a"), tla.name("b"), tla.name("c")))
  }

  test("Test byName: bad calls") {
    assertThrows[NoSuchElementException](bd.byName("not an operator name", NullEx, tla.name("b")))

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, NullEx).untyped())
  }

  test("Test byNameOrNull: bad calls") {
    val nullBadName = bd.byNameOrNull("not an operator name", NullEx, tla.name("b")).untyped()

    assert(nullBadName == NullEx)

    val nullBadArity = bd.byNameOrNull(TlaArithOper.plus.name, NullEx).untyped()

    assert(nullBadArity == NullEx)
  }

  test("Test direct methods: TlaOper") {
    val eqBuild1 = bd.eql(tla.name("a"), tla.name("b")).untyped()
    val eqBuild2 = bd.eql(tla.name("a"), bd.int(2)).untyped()

    assert(eqBuild1 == OperEx(TlaOper.eq, tla.name("a"), tla.name("b")))
    assert(eqBuild2 == OperEx(TlaOper.eq, tla.name("a"), ValEx(TlaInt(2))))

    val neBuild1 = bd.neql(tla.name("a"), tla.name("b")).untyped()
    val neBuild2 = bd.neql(tla.name("a"), bd.int(2)).untyped()

    assert(neBuild1 == OperEx(TlaOper.ne, tla.name("a"), tla.name("b")))
    assert(neBuild2 == OperEx(TlaOper.ne, tla.name("a"), ValEx(TlaInt(2))))

    val applyBuild1 = bd.appOp(tla.name("a")).untyped()
    val applyBuild2 = bd.appOp(tla.name("a"), tla.name("b")).untyped()
    val applyBuild3 = bd.appOp(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val applyBuild4 = bd.appOp(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(applyBuild1 == OperEx(TlaOper.apply, tla.name("a")))
    assert(applyBuild2 == OperEx(TlaOper.apply, tla.name("a"), tla.name("b")))
    assert(applyBuild3 == OperEx(TlaOper.apply, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(applyBuild4 == OperEx(TlaOper.apply, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))

    val chooseBuild1 = bd.choose(tla.name("a"), tla.name("b")).untyped()
    val chooseBuild2 = bd.choose(tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(chooseBuild1 == OperEx(TlaOper.chooseUnbounded, tla.name("a"), tla.name("b")))
    assert(chooseBuild2 == OperEx(TlaOper.chooseBounded, tla.name("a"), tla.name("b"), tla.name("c")))

    val guessBuild = bd.guess(tla.name("S")).untyped()
    assert(guessBuild == OperEx(ApalacheOper.guess, tla.name("S")))
  }

  test("Test byName: TlaOper") {
    val eqBuild = bd.byName(TlaOper.eq.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.eq.name, tla.name("a")).untyped())
    assert(eqBuild == OperEx(TlaOper.eq, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.eq.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val neBuild = bd.byName(TlaOper.ne.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.ne.name, tla.name("a")).untyped())
    assert(neBuild == OperEx(TlaOper.ne, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.ne.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val cbBuild = bd.byName(TlaOper.chooseBounded.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseBounded.name, tla.name("a"), tla.name("b")).untyped())
    assert(cbBuild == OperEx(TlaOper.chooseBounded, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseBounded.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())

    val cubBuild = bd.byName(TlaOper.chooseUnbounded.name, tla.name("a"), tla.name("b")).untyped()

    assert(cubBuild == OperEx(TlaOper.chooseUnbounded, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseUnbounded.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaOper.chooseUnbounded.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
  }

  test("Test byNameOrNull: TlaOper") {
    val eqBuildBad1 = bd.byNameOrNull(TlaOper.eq.name, tla.name("a")).untyped()
    val eqBuild = bd.byNameOrNull(TlaOper.eq.name, tla.name("a"), tla.name("b")).untyped()
    val eqBuildBad2 = bd.byNameOrNull(TlaOper.eq.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(eqBuildBad1 == NullEx)
    assert(eqBuild == OperEx(TlaOper.eq, tla.name("a"), tla.name("b")))
    assert(eqBuildBad2 == NullEx)

    val neBuildBad1 = bd.byNameOrNull(TlaOper.ne.name, tla.name("a")).untyped()
    val neBuild = bd.byNameOrNull(TlaOper.ne.name, tla.name("a"), tla.name("b")).untyped()
    val neBuildBad2 = bd.byNameOrNull(TlaOper.ne.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(neBuildBad1 == NullEx)
    assert(neBuild == OperEx(TlaOper.ne, tla.name("a"), tla.name("b")))
    assert(neBuildBad2 == NullEx)

    val cbBuildBad1 = bd.byNameOrNull(TlaOper.chooseBounded.name, tla.name("a"), tla.name("b")).untyped()
    val cbBuild = bd.byNameOrNull(TlaOper.chooseBounded.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val cbBuildBad2 = bd.byNameOrNull(TlaOper.chooseBounded.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(cbBuildBad1 == NullEx)
    assert(cbBuild == OperEx(TlaOper.chooseBounded, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(cbBuildBad2 == NullEx)

    val cubBuild = bd.byNameOrNull(TlaOper.chooseUnbounded.name, tla.name("a"), tla.name("b")).untyped()
    val cubBuildBad1 = bd.byNameOrNull(TlaOper.chooseUnbounded.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val cubBuildBad2 = bd.byNameOrNull(TlaOper.chooseUnbounded.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(cubBuild == OperEx(TlaOper.chooseUnbounded, tla.name("a"), tla.name("b")))
    assert(cubBuildBad1 == NullEx)
    assert(cubBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaBoolOper ") {
    val andBuild1 = bd.and(tla.name("a")).untyped()
    val andBuild2 = bd.and(tla.name("a"), tla.name("b")).untyped()
    val andBuild3 = bd.and(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val andBuild4 = bd.and(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and, tla.name("a")))
    assert(andBuild2 == OperEx(TlaBoolOper.and, tla.name("a"), tla.name("b")))
    assert(andBuild3 == OperEx(TlaBoolOper.and, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(andBuild4 == OperEx(TlaBoolOper.and, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))

    val orBuild1 = bd.or(tla.name("a")).untyped()
    val orBuild2 = bd.or(tla.name("a"), tla.name("b")).untyped()
    val orBuild3 = bd.or(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val orBuild4 = bd.or(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or, tla.name("a")))
    assert(orBuild2 == OperEx(TlaBoolOper.or, tla.name("a"), tla.name("b")))
    assert(orBuild3 == OperEx(TlaBoolOper.or, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(orBuild4 == OperEx(TlaBoolOper.or, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))

    val notBuild1 = bd.not(tla.name("a")).untyped()

    assert(notBuild1 == OperEx(TlaBoolOper.not, tla.name("a")))

    val impliesBuild1 = bd.impl(tla.name("a"), tla.name("b")).untyped()

    assert(impliesBuild1 == OperEx(TlaBoolOper.implies, tla.name("a"), tla.name("b")))

    val equivBuild1 = bd.equiv(tla.name("a"), tla.name("b")).untyped()

    assert(equivBuild1 == OperEx(TlaBoolOper.equiv, tla.name("a"), tla.name("b")))

    val forallBuild1 = bd.forall(tla.name("a"), tla.name("b")).untyped()
    val forallBuild2 = bd.forall(tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(forallBuild1 == OperEx(TlaBoolOper.forallUnbounded, tla.name("a"), tla.name("b")))
    assert(forallBuild2 == OperEx(TlaBoolOper.forall, tla.name("a"), tla.name("b"), tla.name("c")))

    val existsBuild1 = bd.exists(tla.name("a"), tla.name("b")).untyped()
    val existsBuild2 = bd.exists(tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(existsBuild1 == OperEx(TlaBoolOper.existsUnbounded, tla.name("a"), tla.name("b")))
    assert(existsBuild2 == OperEx(TlaBoolOper.exists, tla.name("a"), tla.name("b"), tla.name("c")))
  }

  test("Test byName: TlaBoolOper ") {
    val andBuild1 = bd.byName(TlaBoolOper.and.name).untyped()
    val andBuild2 = bd.byName(TlaBoolOper.and.name, tla.name("a")).untyped()
    val andBuild3 = bd.byName(TlaBoolOper.and.name, tla.name("a"), tla.name("b")).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and))
    assert(andBuild2 == OperEx(TlaBoolOper.and, tla.name("a")))
    assert(andBuild3 == OperEx(TlaBoolOper.and, tla.name("a"), tla.name("b")))

    val orBuild1 = bd.byName(TlaBoolOper.or.name).untyped()
    val orBuild2 = bd.byName(TlaBoolOper.or.name, tla.name("a")).untyped()
    val orBuild3 = bd.byName(TlaBoolOper.or.name, tla.name("a"), tla.name("b")).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or))
    assert(orBuild2 == OperEx(TlaBoolOper.or, tla.name("a")))
    assert(orBuild3 == OperEx(TlaBoolOper.or, tla.name("a"), tla.name("b")))

    val notBuild = bd.byName(TlaBoolOper.not.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.not.name).untyped())
    assert(notBuild == OperEx(TlaBoolOper.not, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.not.name, tla.name("a"), tla.name("b")).untyped())

    val impliesBuild = bd.byName(TlaBoolOper.implies.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.implies.name, tla.name("a")).untyped())
    assert(impliesBuild == OperEx(TlaBoolOper.implies, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaBoolOper.implies.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

  }

  test("Test byNameOrNull: TlaBoolOper ") {
    val andBuild1 = bd.byNameOrNull(TlaBoolOper.and.name).untyped()
    val andBuild2 = bd.byNameOrNull(TlaBoolOper.and.name, tla.name("a")).untyped()
    val andBuild3 = bd.byNameOrNull(TlaBoolOper.and.name, tla.name("a"), tla.name("b")).untyped()

    assert(andBuild1 == OperEx(TlaBoolOper.and))
    assert(andBuild2 == OperEx(TlaBoolOper.and, tla.name("a")))
    assert(andBuild3 == OperEx(TlaBoolOper.and, tla.name("a"), tla.name("b")))

    val orBuild1 = bd.byNameOrNull(TlaBoolOper.or.name).untyped()
    val orBuild2 = bd.byNameOrNull(TlaBoolOper.or.name, tla.name("a")).untyped()
    val orBuild3 = bd.byNameOrNull(TlaBoolOper.or.name, tla.name("a"), tla.name("b")).untyped()

    assert(orBuild1 == OperEx(TlaBoolOper.or))
    assert(orBuild2 == OperEx(TlaBoolOper.or, tla.name("a")))
    assert(orBuild3 == OperEx(TlaBoolOper.or, tla.name("a"), tla.name("b")))

    val notBuildBad1 = bd.byNameOrNull(TlaBoolOper.not.name).untyped()
    val notBuild = bd.byNameOrNull(TlaBoolOper.not.name, tla.name("a")).untyped()
    val notBuildBad2 = bd.byNameOrNull(TlaBoolOper.not.name, tla.name("a"), tla.name("b")).untyped()

    assert(notBuildBad1 == NullEx)
    assert(notBuild == OperEx(TlaBoolOper.not, tla.name("a")))
    assert(notBuildBad2 == NullEx)

    val impliesBuildBad1 = bd.byNameOrNull(TlaBoolOper.implies.name, tla.name("a")).untyped()
    val impliesBuild = bd.byNameOrNull(TlaBoolOper.implies.name, tla.name("a"), tla.name("b")).untyped()
    val impliesBuildBad2 = bd.byNameOrNull(TlaBoolOper.implies.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(impliesBuildBad1 == NullEx)
    assert(impliesBuild == OperEx(TlaBoolOper.implies, tla.name("a"), tla.name("b")))
    assert(impliesBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaActionOper") {
    val primeBuild1 = bd.prime(tla.name("a")).untyped()
    val primeBuild2 = bd.prime(bd.name("name")).untyped()

    assert(primeBuild1 == OperEx(TlaActionOper.prime, tla.name("a")))
    assert(primeBuild2 == OperEx(TlaActionOper.prime, NameEx("name")))

    val primeEqBuild1 = bd.primeEq(bd.name("name"), tla.name("a")).untyped()
    val primeEqBuild2 = bd.primeEq(tla.name("a"), tla.name("b")).untyped()
    val primeEqBuild3 = bd.primeEq(bd.name("name"), bd.int(1)).untyped()
    val primeEqBuild4 = bd.primeEq(tla.name("a"), bd.int(2)).untyped()
    val primeEqBuild5 = bd.primeEq(bd.name("name1"), bd.name("name2")).untyped()

    assert(primeEqBuild1 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name")), tla.name("a")))
    assert(primeEqBuild2 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, tla.name("a")), tla.name("b")))
    assert(primeEqBuild3 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name")), ValEx(TlaInt(1))))
    assert(primeEqBuild4 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, tla.name("a")), ValEx(TlaInt(2))))
    assert(primeEqBuild5 == OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("name1")), NameEx("name2")))

    val stutterBuild = bd.stutt(tla.name("a"), tla.name("b")).untyped()

    assert(stutterBuild == OperEx(TlaActionOper.stutter, tla.name("a"), tla.name("b")))

    val nostutterBuild = bd.nostutt(tla.name("a"), tla.name("b")).untyped()

    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, tla.name("a"), tla.name("b")))

    val enabledBuild = bd.enabled(tla.name("a")).untyped()

    assert(enabledBuild == OperEx(TlaActionOper.enabled, tla.name("a")))

    val unchangedBuild = bd.unchanged(tla.name("a")).untyped()

    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, tla.name("a")))

    val compositionBuild = bd.comp(tla.name("a"), tla.name("b")).untyped()

    assert(compositionBuild == OperEx(TlaActionOper.composition, tla.name("a"), tla.name("b")))

  }

  test("Test byName: TlaActionOper") {
    val primeBuild = bd.byNameOrNull(TlaActionOper.prime.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.prime.name).untyped())
    assert(primeBuild == OperEx(TlaActionOper.prime, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.prime.name, tla.name("a"), tla.name("b")).untyped())

    val stutterBuild = bd.byName(TlaActionOper.stutter.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.stutter.name, tla.name("a")).untyped())
    assert(stutterBuild == OperEx(TlaActionOper.stutter, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.stutter.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val nostutterBuild = bd.byName(TlaActionOper.nostutter.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.nostutter.name, tla.name("a")).untyped())
    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.nostutter.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val enabledBuild = bd.byName(TlaActionOper.enabled.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.enabled.name).untyped())
    assert(enabledBuild == OperEx(TlaActionOper.enabled, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.enabled.name, tla.name("a"), tla.name("b")).untyped())

    val unchangedBuild = bd.byName(TlaActionOper.unchanged.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.unchanged.name).untyped())
    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.unchanged.name, tla.name("a"), tla.name("b")).untyped())

    val compositionBuild = bd.byName(TlaActionOper.composition.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.composition.name, tla.name("a")).untyped())
    assert(compositionBuild == OperEx(TlaActionOper.composition, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaActionOper.composition.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())
  }

  test("Test byNameOrNull: TlaActionOper") {
    val primeBuildBad1 = bd.byNameOrNull(TlaActionOper.prime.name).untyped()
    val primeBuild = bd.byNameOrNull(TlaActionOper.prime.name, tla.name("a")).untyped()
    val primeBuildBad2 = bd.byNameOrNull(TlaActionOper.prime.name, tla.name("a"), tla.name("b")).untyped()

    assert(primeBuildBad1 == NullEx)
    assert(primeBuild == OperEx(TlaActionOper.prime, tla.name("a")))
    assert(primeBuildBad2 == NullEx)

    val stutterBuildBad1 = bd.byNameOrNull(TlaActionOper.stutter.name, tla.name("a")).untyped()
    val stutterBuild = bd.byNameOrNull(TlaActionOper.stutter.name, tla.name("a"), tla.name("b")).untyped()
    val stutterBuildBad2 = bd.byNameOrNull(TlaActionOper.stutter.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(stutterBuildBad1 == NullEx)
    assert(stutterBuild == OperEx(TlaActionOper.stutter, tla.name("a"), tla.name("b")))
    assert(stutterBuildBad2 == NullEx)

    val nostutterBuildBad1 = bd.byNameOrNull(TlaActionOper.nostutter.name, tla.name("a")).untyped()
    val nostutterBuild = bd.byNameOrNull(TlaActionOper.nostutter.name, tla.name("a"), tla.name("b")).untyped()
    val nostutterBuildBad2 = bd.byNameOrNull(TlaActionOper.nostutter.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(nostutterBuildBad1 == NullEx)
    assert(nostutterBuild == OperEx(TlaActionOper.nostutter, tla.name("a"), tla.name("b")))
    assert(nostutterBuildBad2 == NullEx)

    val enabledBuildBad1 = bd.byNameOrNull(TlaActionOper.enabled.name).untyped()
    val enabledBuild = bd.byNameOrNull(TlaActionOper.enabled.name, tla.name("a")).untyped()
    val enabledBuildBad2 = bd.byNameOrNull(TlaActionOper.enabled.name, tla.name("a"), tla.name("b")).untyped()

    assert(enabledBuildBad1 == NullEx)
    assert(enabledBuild == OperEx(TlaActionOper.enabled, tla.name("a")))
    assert(enabledBuildBad2 == NullEx)

    val unchangedBuildBad1 = bd.byNameOrNull(TlaActionOper.unchanged.name).untyped()
    val unchangedBuild = bd.byNameOrNull(TlaActionOper.unchanged.name, tla.name("a")).untyped()
    val unchangedBuildBad2 = bd.byNameOrNull(TlaActionOper.unchanged.name, tla.name("a"), tla.name("b")).untyped()

    assert(unchangedBuildBad1 == NullEx)
    assert(unchangedBuild == OperEx(TlaActionOper.unchanged, tla.name("a")))
    assert(unchangedBuildBad2 == NullEx)

    val compositionBuildBad1 = bd.byNameOrNull(TlaActionOper.composition.name, tla.name("a")).untyped()
    val compositionBuild = bd.byNameOrNull(TlaActionOper.composition.name, tla.name("a"), tla.name("b")).untyped()
    val compositionBuildBad2 = bd.byNameOrNull(TlaActionOper.composition.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(compositionBuildBad1 == NullEx)
    assert(compositionBuild == OperEx(TlaActionOper.composition, tla.name("a"), tla.name("b")))
    assert(compositionBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaControlOper") {

    val caseBuild1 = bd.caseAny(tla.name("a"), tla.name("b")).untyped()
    val caseBuild2 = bd.caseAny(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val caseBuild3 = bd.caseAny(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val caseBuild4 = bd.caseAny(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()
    val caseBuild5 = bd.caseAny(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped()
    val caseBuild6 = bd.caseAny(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b")))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")))

    val caseSplitBuild1 = bd.caseSplit(tla.name("a"), tla.name("b")).untyped()
    val caseSplitBuild2 = bd.caseSplit(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val caseSplitBuild3 = bd.caseSplit(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped()

    assert(caseSplitBuild1 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.caseSplit(tla.name("a"), tla.name("b"), tla.name("c")).untyped())
    assert(caseSplitBuild2 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assertThrows[IllegalArgumentException](bd.caseSplit(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped())
    assert(caseSplitBuild3 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")))

    val caseOtherBuild1 = bd.caseOther(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val caseOtherBuild2 = bd.caseOther(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()
    val caseOtherBuild3 = bd.caseOther(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")).untyped()

    assert(caseOtherBuild1 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.caseOther(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(caseOtherBuild2 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assertThrows[IllegalArgumentException](bd.caseOther(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped())
    assert(caseOtherBuild3 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")))

    val iteBuild1 = bd.ite(tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(iteBuild1 == OperEx(TlaControlOper.ifThenElse, tla.name("a"), tla.name("b"), tla.name("c")))

    //    val letInBuild1 = bd.letIn( tla.name("a"), TlaOperDecl( "b" , List(), tla.name("c") ) )
    //    val letInBuild2 =
    //      bd.letIn(
    //        tla.name("a"),
    //        TlaOperDecl(
    //          "b" ,
    //          List(
    //            SimpleFormalParam( "x" ),
    //            OperFormalParam( "f", FixedArity( 0 ) )
    //          ),
    //          tla.name("c")
    //        )
    //      )
    //
    //    assert( letInBuild1 == OperEx( new LetInOper( List(TlaOperDecl( "b" , List(), tla.name("c") ) ) ), tla.name("a") ) )

  }

  test("Test byName: TlaControlOper") {
    val caseBuild1 = bd.byName(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b")).untyped()
    val caseBuild2 = bd.byName(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val caseBuild3 = bd.byName(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val caseBuild4 = bd.byName(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()
    val caseBuild5 = bd.byName(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped()
    val caseBuild6 = bd.byName(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b")))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")))

    val caseNoOtherBuild = bd.byName(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseNoOther.name).untyped())
    assert(caseNoOtherBuild == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val caseWithOtherBuild = bd.byName(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name, tla.name("a")).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b")).untyped())
    assert(caseWithOtherBuild == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c")))

    val iteBuild = bd.byName(TlaControlOper.ifThenElse.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.ifThenElse.name, tla.name("a"), tla.name("b")).untyped())
    assert(iteBuild == OperEx(TlaControlOper.ifThenElse, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.byName(TlaControlOper.ifThenElse.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
  }

  test("Test byNameOrNull: TlaControlOper") {
    val caseBuild1 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b")).untyped()
    val caseBuild2 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val caseBuild3 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val caseBuild4 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()
    val caseBuild5 = bd.byNameOrNull(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped()
    val caseBuild6 = bd.byNameOrNull(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")).untyped()

    assert(caseBuild1 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b")))
    assert(caseBuild2 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(caseBuild3 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assert(caseBuild4 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assert(caseBuild5 == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")))
    assert(caseBuild6 == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f"), tla.name("g")))

    val caseNoOtherBuildEmpty = bd.byNameOrNull(TlaControlOper.caseNoOther.name).untyped()
    val caseNoOtherBuild = bd.byNameOrNull(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b")).untyped()
    val caseNoOtherBuildBad = bd.byNameOrNull(TlaControlOper.caseNoOther.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(caseNoOtherBuildEmpty == NullEx)
    assert(caseNoOtherBuild == OperEx(TlaControlOper.caseNoOther, tla.name("a"), tla.name("b")))
    assert(caseNoOtherBuildBad == NullEx)

    val caseWithOtherBuildEmpty = bd.byNameOrNull(TlaControlOper.caseWithOther.name).untyped()
    val caseWithOtherBuildSingle = bd.byNameOrNull(TlaControlOper.caseWithOther.name, tla.name("a")).untyped()
    val caseWithOtherBuildBad = bd.byNameOrNull(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b")).untyped()
    val caseWithOtherBuild = bd.byNameOrNull(TlaControlOper.caseWithOther.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(caseWithOtherBuildEmpty == NullEx)
    assert(caseWithOtherBuildSingle == NullEx)
    assert(caseWithOtherBuildBad == NullEx)
    assert(caseWithOtherBuild == OperEx(TlaControlOper.caseWithOther, tla.name("a"), tla.name("b"), tla.name("c")))

    val iteBuildBad1 = bd.byNameOrNull(TlaControlOper.ifThenElse.name, tla.name("a"), tla.name("b")).untyped()
    val iteBuild = bd.byNameOrNull(TlaControlOper.ifThenElse.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val iteBuildBad2 = bd.byNameOrNull(TlaControlOper.ifThenElse.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(iteBuildBad1 == NullEx)
    assert(iteBuild == OperEx(TlaControlOper.ifThenElse, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(iteBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaTempOper") {
    val AABuild = bd.AA(tla.name("a"), tla.name("b")).untyped()

    assert(AABuild == OperEx(TlaTempOper.AA, tla.name("a"), tla.name("b")))

    val EEBuild = bd.EE(tla.name("a"), tla.name("b")).untyped()

    assert(EEBuild == OperEx(TlaTempOper.EE, tla.name("a"), tla.name("b")))

    val boxBuild = bd.box(tla.name("a")).untyped()

    assert(boxBuild == OperEx(TlaTempOper.box, tla.name("a")))

    val diamondBuild = bd.diamond(tla.name("a")).untyped()

    assert(diamondBuild == OperEx(TlaTempOper.diamond, tla.name("a")))

    val leadsToBuild = bd.leadsTo(tla.name("a"), tla.name("b")).untyped()

    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, tla.name("a"), tla.name("b")))

    val guaranteesBuild = bd.guarantees(tla.name("a"), tla.name("b")).untyped()

    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, tla.name("a"), tla.name("b")))

    val strongFairnessBuild = bd.SF(tla.name("a"), tla.name("b")).untyped()

    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, tla.name("a"), tla.name("b")))

    val weakFairnessBuild = bd.WF(tla.name("a"), tla.name("b")).untyped()

    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, tla.name("a"), tla.name("b")))
  }

  test("Test byName: TlaTempOper") {
    val AABuild = bd.byName(TlaTempOper.AA.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.AA.name, tla.name("a")).untyped())
    assert(AABuild == OperEx(TlaTempOper.AA, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.AA.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val EEBuild = bd.byName(TlaTempOper.EE.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.EE.name, tla.name("a")).untyped())
    assert(EEBuild == OperEx(TlaTempOper.EE, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.EE.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val boxBuild = bd.byName(TlaTempOper.box.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.box.name).untyped())
    assert(boxBuild == OperEx(TlaTempOper.box, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.box.name, tla.name("a"), tla.name("b")).untyped())

    val diamondBuild = bd.byName(TlaTempOper.diamond.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.diamond.name).untyped())
    assert(diamondBuild == OperEx(TlaTempOper.diamond, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.diamond.name, tla.name("a"), tla.name("b")).untyped())

    val leadsToBuild = bd.byName(TlaTempOper.leadsTo.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.leadsTo.name, tla.name("a")).untyped())
    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.leadsTo.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val guaranteesBuild = bd.byName(TlaTempOper.guarantees.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.guarantees.name, tla.name("a")).untyped())
    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.guarantees.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val strongFairnessBuild = bd.byName(TlaTempOper.strongFairness.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.strongFairness.name, tla.name("a")).untyped())
    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.strongFairness.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val weakFairnessBuild = bd.byName(TlaTempOper.weakFairness.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.weakFairness.name, tla.name("a")).untyped())
    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaTempOper.weakFairness.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

  }

  test("Test byNameOrNull: TlaTempOper") {
    val AABuildBad1 = bd.byNameOrNull(TlaTempOper.AA.name, tla.name("a")).untyped()
    val AABuild = bd.byNameOrNull(TlaTempOper.AA.name, tla.name("a"), tla.name("b")).untyped()
    val AABuildBad2 = bd.byNameOrNull(TlaTempOper.AA.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(AABuildBad1 == NullEx)
    assert(AABuild == OperEx(TlaTempOper.AA, tla.name("a"), tla.name("b")))
    assert(AABuildBad2 == NullEx)

    val EEBuildBad1 = bd.byNameOrNull(TlaTempOper.EE.name, tla.name("a")).untyped()
    val EEBuild = bd.byNameOrNull(TlaTempOper.EE.name, tla.name("a"), tla.name("b")).untyped()
    val EEBuildBad2 = bd.byNameOrNull(TlaTempOper.EE.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(EEBuildBad1 == NullEx)
    assert(EEBuild == OperEx(TlaTempOper.EE, tla.name("a"), tla.name("b")))
    assert(EEBuildBad2 == NullEx)

    val boxBuildBad1 = bd.byNameOrNull(TlaTempOper.box.name).untyped()
    val boxBuild = bd.byNameOrNull(TlaTempOper.box.name, tla.name("a")).untyped()
    val boxBuildBad2 = bd.byNameOrNull(TlaTempOper.box.name, tla.name("a"), tla.name("b")).untyped()

    assert(boxBuildBad1 == NullEx)
    assert(boxBuild == OperEx(TlaTempOper.box, tla.name("a")))
    assert(boxBuildBad2 == NullEx)

    val diamondBuildBad1 = bd.byNameOrNull(TlaTempOper.diamond.name).untyped()
    val diamondBuild = bd.byNameOrNull(TlaTempOper.diamond.name, tla.name("a")).untyped()
    val diamondBuildBad2 = bd.byNameOrNull(TlaTempOper.diamond.name, tla.name("a"), tla.name("b")).untyped()

    assert(diamondBuildBad1 == NullEx)
    assert(diamondBuild == OperEx(TlaTempOper.diamond, tla.name("a")))
    assert(diamondBuildBad2 == NullEx)

    val leadsToBuildBad1 = bd.byNameOrNull(TlaTempOper.leadsTo.name, tla.name("a")).untyped()
    val leadsToBuild = bd.byNameOrNull(TlaTempOper.leadsTo.name, tla.name("a"), tla.name("b")).untyped()
    val leadsToBuildBad2 = bd.byNameOrNull(TlaTempOper.leadsTo.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(leadsToBuildBad1 == NullEx)
    assert(leadsToBuild == OperEx(TlaTempOper.leadsTo, tla.name("a"), tla.name("b")))
    assert(leadsToBuildBad2 == NullEx)

    val guaranteesBuildBad1 = bd.byNameOrNull(TlaTempOper.guarantees.name, tla.name("a")).untyped()
    val guaranteesBuild = bd.byNameOrNull(TlaTempOper.guarantees.name, tla.name("a"), tla.name("b")).untyped()
    val guaranteesBuildBad2 = bd.byNameOrNull(TlaTempOper.guarantees.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(guaranteesBuildBad1 == NullEx)
    assert(guaranteesBuild == OperEx(TlaTempOper.guarantees, tla.name("a"), tla.name("b")))
    assert(guaranteesBuildBad2 == NullEx)

    val strongFairnessBuildBad1 = bd.byNameOrNull(TlaTempOper.strongFairness.name, tla.name("a")).untyped()
    val strongFairnessBuild = bd.byNameOrNull(TlaTempOper.strongFairness.name, tla.name("a"), tla.name("b")).untyped()
    val strongFairnessBuildBad2 = bd.byNameOrNull(TlaTempOper.strongFairness.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(strongFairnessBuildBad1 == NullEx)
    assert(strongFairnessBuild == OperEx(TlaTempOper.strongFairness, tla.name("a"), tla.name("b")))
    assert(strongFairnessBuildBad2 == NullEx)

    val weakFairnessBuildBad1 = bd.byNameOrNull(TlaTempOper.weakFairness.name, tla.name("a")).untyped()
    val weakFairnessBuild = bd.byNameOrNull(TlaTempOper.weakFairness.name, tla.name("a"), tla.name("b")).untyped()
    val weakFairnessBuildBad2 = bd.byNameOrNull(TlaTempOper.weakFairness.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(weakFairnessBuildBad1 == NullEx)
    assert(weakFairnessBuild == OperEx(TlaTempOper.weakFairness, tla.name("a"), tla.name("b")))
    assert(weakFairnessBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaArithOper") {

    val plusBuild1 = bd.plus(tla.name("a"), tla.name("b")).untyped()
    val plusBuild2 = bd.plus(tla.name("a"), bd.int(2)).untyped()
    val plusBuild3 = bd.plus(bd.int(1), tla.name("b")).untyped()
    val plusBuild4 = bd.plus(bd.int(1), bd.int(2)).untyped()

    assert(plusBuild1 == OperEx(TlaArithOper.plus, tla.name("a"), tla.name("b")))
    assert(plusBuild2 == OperEx(TlaArithOper.plus, tla.name("a"), ValEx(TlaInt(2))))
    assert(plusBuild3 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), tla.name("b")))
    assert(plusBuild4 == OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val minusBuild1 = bd.minus(tla.name("a"), tla.name("b")).untyped()
    val minusBuild2 = bd.minus(tla.name("a"), bd.int(2)).untyped()
    val minusBuild3 = bd.minus(bd.int(1), tla.name("b")).untyped()
    val minusBuild4 = bd.minus(bd.int(1), bd.int(2)).untyped()

    assert(minusBuild1 == OperEx(TlaArithOper.minus, tla.name("a"), tla.name("b")))
    assert(minusBuild2 == OperEx(TlaArithOper.minus, tla.name("a"), ValEx(TlaInt(2))))
    assert(minusBuild3 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), tla.name("b")))
    assert(minusBuild4 == OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val uminusBuild = bd.uminus(tla.name("a")).untyped()

    assert(uminusBuild == OperEx(TlaArithOper.uminus, tla.name("a")))

    val multBuild1 = bd.mult(tla.name("a"), tla.name("b")).untyped()
    val multBuild2 = bd.mult(tla.name("a"), bd.int(2)).untyped()
    val multBuild3 = bd.mult(bd.int(1), tla.name("b")).untyped()
    val multBuild4 = bd.mult(bd.int(1), bd.int(2)).untyped()

    assert(multBuild1 == OperEx(TlaArithOper.mult, tla.name("a"), tla.name("b")))
    assert(multBuild2 == OperEx(TlaArithOper.mult, tla.name("a"), ValEx(TlaInt(2))))
    assert(multBuild3 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), tla.name("b")))
    assert(multBuild4 == OperEx(TlaArithOper.mult, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val divBuild1 = bd.div(tla.name("a"), tla.name("b")).untyped()
    val divBuild2 = bd.div(tla.name("a"), bd.int(2)).untyped()
    val divBuild3 = bd.div(bd.int(1), tla.name("b")).untyped()
    val divBuild4 = bd.div(bd.int(1), bd.int(2)).untyped()

    assert(divBuild1 == OperEx(TlaArithOper.div, tla.name("a"), tla.name("b")))
    assert(divBuild2 == OperEx(TlaArithOper.div, tla.name("a"), ValEx(TlaInt(2))))
    assert(divBuild3 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), tla.name("b")))
    assert(divBuild4 == OperEx(TlaArithOper.div, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val modBuild1 = bd.mod(tla.name("a"), tla.name("b")).untyped()
    val modBuild2 = bd.mod(tla.name("a"), bd.int(2)).untyped()
    val modBuild3 = bd.mod(bd.int(1), tla.name("b")).untyped()
    val modBuild4 = bd.mod(bd.int(1), bd.int(2)).untyped()

    assert(modBuild1 == OperEx(TlaArithOper.mod, tla.name("a"), tla.name("b")))
    assert(modBuild2 == OperEx(TlaArithOper.mod, tla.name("a"), ValEx(TlaInt(2))))
    assert(modBuild3 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), tla.name("b")))
    assert(modBuild4 == OperEx(TlaArithOper.mod, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val realDivBuild1 = bd.rDiv(tla.name("a"), tla.name("b")).untyped()
    val realDivBuild2 = bd.rDiv(tla.name("a"), bd.int(2)).untyped()
    val realDivBuild3 = bd.rDiv(bd.int(1), tla.name("b")).untyped()
    val realDivBuild4 = bd.rDiv(bd.int(1), bd.int(2)).untyped()

    assert(realDivBuild1 == OperEx(TlaArithOper.realDiv, tla.name("a"), tla.name("b")))
    assert(realDivBuild2 == OperEx(TlaArithOper.realDiv, tla.name("a"), ValEx(TlaInt(2))))
    assert(realDivBuild3 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), tla.name("b")))
    assert(realDivBuild4 == OperEx(TlaArithOper.realDiv, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val expBuild1 = bd.exp(tla.name("a"), tla.name("b")).untyped()
    val expBuild2 = bd.exp(tla.name("a"), bd.int(2)).untyped()
    val expBuild3 = bd.exp(bd.int(1), tla.name("b")).untyped()
    val expBuild4 = bd.exp(bd.int(1), bd.int(2)).untyped()

    assert(expBuild1 == OperEx(TlaArithOper.exp, tla.name("a"), tla.name("b")))
    assert(expBuild2 == OperEx(TlaArithOper.exp, tla.name("a"), ValEx(TlaInt(2))))
    assert(expBuild3 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), tla.name("b")))
    assert(expBuild4 == OperEx(TlaArithOper.exp, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val dotdotBuild1 = bd.dotdot(tla.name("a"), tla.name("b")).untyped()
    val dotdotBuild2 = bd.dotdot(tla.name("a"), bd.int(2)).untyped()
    val dotdotBuild3 = bd.dotdot(bd.int(1), tla.name("b")).untyped()
    val dotdotBuild4 = bd.dotdot(bd.int(1), bd.int(2)).untyped()

    assert(dotdotBuild1 == OperEx(TlaArithOper.dotdot, tla.name("a"), tla.name("b")))
    assert(dotdotBuild2 == OperEx(TlaArithOper.dotdot, tla.name("a"), ValEx(TlaInt(2))))
    assert(dotdotBuild3 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), tla.name("b")))
    assert(dotdotBuild4 == OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val ltBuild1 = bd.lt(tla.name("a"), tla.name("b")).untyped()
    val ltBuild2 = bd.lt(tla.name("a"), bd.int(2)).untyped()
    val ltBuild3 = bd.lt(bd.int(1), tla.name("b")).untyped()
    val ltBuild4 = bd.lt(bd.int(1), bd.int(2)).untyped()

    assert(ltBuild1 == OperEx(TlaArithOper.lt, tla.name("a"), tla.name("b")))
    assert(ltBuild2 == OperEx(TlaArithOper.lt, tla.name("a"), ValEx(TlaInt(2))))
    assert(ltBuild3 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), tla.name("b")))
    assert(ltBuild4 == OperEx(TlaArithOper.lt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val gtBuild1 = bd.gt(tla.name("a"), tla.name("b")).untyped()
    val gtBuild2 = bd.gt(tla.name("a"), bd.int(2)).untyped()
    val gtBuild3 = bd.gt(bd.int(1), tla.name("b")).untyped()
    val gtBuild4 = bd.gt(bd.int(1), bd.int(2)).untyped()

    assert(gtBuild1 == OperEx(TlaArithOper.gt, tla.name("a"), tla.name("b")))
    assert(gtBuild2 == OperEx(TlaArithOper.gt, tla.name("a"), ValEx(TlaInt(2))))
    assert(gtBuild3 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), tla.name("b")))
    assert(gtBuild4 == OperEx(TlaArithOper.gt, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val leBuild1 = bd.le(tla.name("a"), tla.name("b")).untyped()
    val leBuild2 = bd.le(tla.name("a"), bd.int(2)).untyped()
    val leBuild3 = bd.le(bd.int(1), tla.name("b")).untyped()
    val leBuild4 = bd.le(bd.int(1), bd.int(2)).untyped()

    assert(leBuild1 == OperEx(TlaArithOper.le, tla.name("a"), tla.name("b")))
    assert(leBuild2 == OperEx(TlaArithOper.le, tla.name("a"), ValEx(TlaInt(2))))
    assert(leBuild3 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), tla.name("b")))
    assert(leBuild4 == OperEx(TlaArithOper.le, ValEx(TlaInt(1)), ValEx(TlaInt(2))))

    val geBuild1 = bd.ge(tla.name("a"), tla.name("b")).untyped()
    val geBuild2 = bd.ge(tla.name("a"), bd.int(2)).untyped()
    val geBuild3 = bd.ge(bd.int(1), tla.name("b")).untyped()
    val geBuild4 = bd.ge(bd.int(1), bd.int(2)).untyped()

    assert(geBuild1 == OperEx(TlaArithOper.ge, tla.name("a"), tla.name("b")))
    assert(geBuild2 == OperEx(TlaArithOper.ge, tla.name("a"), ValEx(TlaInt(2))))
    assert(geBuild3 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), tla.name("b")))
    assert(geBuild4 == OperEx(TlaArithOper.ge, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
  }

  test("Test byName: TlaArithOper") {

    val plusBuild = bd.byName(TlaArithOper.plus.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, tla.name("a")).untyped())
    assert(plusBuild == OperEx(TlaArithOper.plus, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.plus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val minusBuild = bd.byName(TlaArithOper.minus.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.minus.name, tla.name("a")).untyped())
    assert(minusBuild == OperEx(TlaArithOper.minus, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.minus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val uminusBuild = bd.byName(TlaArithOper.uminus.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.uminus.name).untyped())
    assert(uminusBuild == OperEx(TlaArithOper.uminus, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.uminus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val multBuild = bd.byName(TlaArithOper.mult.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mult.name, tla.name("a")).untyped())
    assert(multBuild == OperEx(TlaArithOper.mult, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mult.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val divBuild = bd.byName(TlaArithOper.div.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.div.name, tla.name("a")).untyped())
    assert(divBuild == OperEx(TlaArithOper.div, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.div.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val modBuild = bd.byName(TlaArithOper.mod.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mod.name, tla.name("a")).untyped())
    assert(modBuild == OperEx(TlaArithOper.mod, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.mod.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val realDivBuild = bd.byName(TlaArithOper.realDiv.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.realDiv.name, tla.name("a")).untyped())
    assert(realDivBuild == OperEx(TlaArithOper.realDiv, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.realDiv.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val expBuild = bd.byName(TlaArithOper.exp.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.exp.name, tla.name("a")).untyped())
    assert(expBuild == OperEx(TlaArithOper.exp, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.exp.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val dotdotBuild = bd.byName(TlaArithOper.dotdot.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.dotdot.name, tla.name("a")).untyped())
    assert(dotdotBuild == OperEx(TlaArithOper.dotdot, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.dotdot.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val ltBuild = bd.byName(TlaArithOper.lt.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.lt.name, tla.name("a")).untyped())
    assert(ltBuild == OperEx(TlaArithOper.lt, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.lt.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val gtBuild = bd.byName(TlaArithOper.gt.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.gt.name, tla.name("a")).untyped())
    assert(gtBuild == OperEx(TlaArithOper.gt, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.gt.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val leBuild = bd.byName(TlaArithOper.le.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.le.name, tla.name("a")).untyped())
    assert(leBuild == OperEx(TlaArithOper.le, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.le.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val geBuild = bd.byName(TlaArithOper.ge.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.ge.name, tla.name("a")).untyped())
    assert(geBuild == OperEx(TlaArithOper.ge, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaArithOper.ge.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())
  }

  test("Test byNameOrNull: TlaArithOper") {

    val plusBuildBad1 = bd.byNameOrNull(TlaArithOper.plus.name, tla.name("a")).untyped()
    val plusBuild = bd.byNameOrNull(TlaArithOper.plus.name, tla.name("a"), tla.name("b")).untyped()
    val plusBuildBad2 = bd.byNameOrNull(TlaArithOper.plus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(plusBuildBad1 == NullEx)
    assert(plusBuild == OperEx(TlaArithOper.plus, tla.name("a"), tla.name("b")))
    assert(plusBuildBad2 == NullEx)

    val minusBuildBad1 = bd.byNameOrNull(TlaArithOper.minus.name, tla.name("a")).untyped()
    val minusBuild = bd.byNameOrNull(TlaArithOper.minus.name, tla.name("a"), tla.name("b")).untyped()
    val minusBuildBad2 = bd.byNameOrNull(TlaArithOper.minus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(minusBuildBad1 == NullEx)
    assert(minusBuild == OperEx(TlaArithOper.minus, tla.name("a"), tla.name("b")))
    assert(minusBuildBad2 == NullEx)

    val uminusBuildBad1 = bd.byNameOrNull(TlaArithOper.uminus.name).untyped()
    val uminusBuild = bd.byNameOrNull(TlaArithOper.uminus.name, tla.name("a")).untyped()
    val uminusBuildBad2 = bd.byNameOrNull(TlaArithOper.uminus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(uminusBuildBad1 == NullEx)
    assert(uminusBuild == OperEx(TlaArithOper.uminus, tla.name("a")))
    assert(uminusBuildBad2 == NullEx)

    val multBuildBad1 = bd.byNameOrNull(TlaArithOper.mult.name, tla.name("a")).untyped()
    val multBuild = bd.byNameOrNull(TlaArithOper.mult.name, tla.name("a"), tla.name("b")).untyped()
    val multBuildBad2 = bd.byNameOrNull(TlaArithOper.mult.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(multBuildBad1 == NullEx)
    assert(multBuild == OperEx(TlaArithOper.mult, tla.name("a"), tla.name("b")))
    assert(multBuildBad2 == NullEx)

    val divBuildBad1 = bd.byNameOrNull(TlaArithOper.div.name, tla.name("a")).untyped()
    val divBuild = bd.byNameOrNull(TlaArithOper.div.name, tla.name("a"), tla.name("b")).untyped()
    val divBuildBad2 = bd.byNameOrNull(TlaArithOper.div.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(divBuildBad1 == NullEx)
    assert(divBuild == OperEx(TlaArithOper.div, tla.name("a"), tla.name("b")))
    assert(divBuildBad2 == NullEx)

    val modBuildBad1 = bd.byNameOrNull(TlaArithOper.mod.name, tla.name("a")).untyped()
    val modBuild = bd.byNameOrNull(TlaArithOper.mod.name, tla.name("a"), tla.name("b")).untyped()
    val modBuildBad2 = bd.byNameOrNull(TlaArithOper.mod.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(modBuildBad1 == NullEx)
    assert(modBuild == OperEx(TlaArithOper.mod, tla.name("a"), tla.name("b")))
    assert(modBuildBad2 == NullEx)

    val realDivBuildBad1 = bd.byNameOrNull(TlaArithOper.realDiv.name, tla.name("a")).untyped()
    val realDivBuild = bd.byNameOrNull(TlaArithOper.realDiv.name, tla.name("a"), tla.name("b")).untyped()
    val realDivBuildBad2 = bd.byNameOrNull(TlaArithOper.realDiv.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(realDivBuildBad1 == NullEx)
    assert(realDivBuild == OperEx(TlaArithOper.realDiv, tla.name("a"), tla.name("b")))
    assert(realDivBuildBad2 == NullEx)

    val expBuildBad1 = bd.byNameOrNull(TlaArithOper.exp.name, tla.name("a")).untyped()
    val expBuild = bd.byNameOrNull(TlaArithOper.exp.name, tla.name("a"), tla.name("b")).untyped()
    val expBuildBad2 = bd.byNameOrNull(TlaArithOper.exp.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(expBuildBad1 == NullEx)
    assert(expBuild == OperEx(TlaArithOper.exp, tla.name("a"), tla.name("b")))
    assert(expBuildBad2 == NullEx)

    val dotdotBuildBad1 = bd.byNameOrNull(TlaArithOper.dotdot.name, tla.name("a")).untyped()
    val dotdotBuild = bd.byNameOrNull(TlaArithOper.dotdot.name, tla.name("a"), tla.name("b")).untyped()
    val dotdotBuildBad2 = bd.byNameOrNull(TlaArithOper.dotdot.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(dotdotBuildBad1 == NullEx)
    assert(dotdotBuild == OperEx(TlaArithOper.dotdot, tla.name("a"), tla.name("b")))
    assert(dotdotBuildBad2 == NullEx)

    val ltBuildBad1 = bd.byNameOrNull(TlaArithOper.lt.name, tla.name("a")).untyped()
    val ltBuild = bd.byNameOrNull(TlaArithOper.lt.name, tla.name("a"), tla.name("b")).untyped()
    val ltBuildBad2 = bd.byNameOrNull(TlaArithOper.lt.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(ltBuildBad1 == NullEx)
    assert(ltBuild == OperEx(TlaArithOper.lt, tla.name("a"), tla.name("b")))
    assert(ltBuildBad2 == NullEx)

    val gtBuildBad1 = bd.byNameOrNull(TlaArithOper.gt.name, tla.name("a")).untyped()
    val gtBuild = bd.byNameOrNull(TlaArithOper.gt.name, tla.name("a"), tla.name("b")).untyped()
    val gtBuildBad2 = bd.byNameOrNull(TlaArithOper.gt.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(gtBuildBad1 == NullEx)
    assert(gtBuild == OperEx(TlaArithOper.gt, tla.name("a"), tla.name("b")))
    assert(gtBuildBad2 == NullEx)

    val leBuildBad1 = bd.byNameOrNull(TlaArithOper.le.name, tla.name("a")).untyped()
    val leBuild = bd.byNameOrNull(TlaArithOper.le.name, tla.name("a"), tla.name("b")).untyped()
    val leBuildBad2 = bd.byNameOrNull(TlaArithOper.le.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(leBuildBad1 == NullEx)
    assert(leBuild == OperEx(TlaArithOper.le, tla.name("a"), tla.name("b")))
    assert(leBuildBad2 == NullEx)

    val geBuildBad1 = bd.byNameOrNull(TlaArithOper.ge.name, tla.name("a")).untyped()
    val geBuild = bd.byNameOrNull(TlaArithOper.ge.name, tla.name("a"), tla.name("b")).untyped()
    val geBuildBad2 = bd.byNameOrNull(TlaArithOper.ge.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(geBuildBad1 == NullEx)
    assert(geBuild == OperEx(TlaArithOper.ge, tla.name("a"), tla.name("b")))
    assert(geBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaFiniteSetOper") {
    val cardinalityBuild = bd.card(tla.name("a")).untyped()

    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, tla.name("a")))

    val isFiniteSetBuild = bd.isFin(tla.name("a")).untyped()

    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, tla.name("a")))
  }

  test("Test byName: TlaFiniteSetOper") {
    val cardinalityBuild = bd.byName(TlaFiniteSetOper.cardinality.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.cardinality.name).untyped())
    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.cardinality.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val isFiniteSetBuild = bd.byName(TlaFiniteSetOper.isFiniteSet.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.isFiniteSet.name).untyped())
    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFiniteSetOper.isFiniteSet.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())
  }

  test("Test byNameOrNull: TlaFiniteSetOper") {
    val cardinalityBuildBad1 = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name).untyped()
    val cardinalityBuild = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name, tla.name("a")).untyped()
    val cardinalityBuildBad2 = bd.byNameOrNull(TlaFiniteSetOper.cardinality.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(cardinalityBuildBad1 == NullEx)
    assert(cardinalityBuild == OperEx(TlaFiniteSetOper.cardinality, tla.name("a")))
    assert(cardinalityBuildBad2 == NullEx)

    val isFiniteSetBuildBad1 = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name).untyped()
    val isFiniteSetBuild = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name, tla.name("a")).untyped()
    val isFiniteSetBuildBad2 = bd.byNameOrNull(TlaFiniteSetOper.isFiniteSet.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(isFiniteSetBuildBad1 == NullEx)
    assert(isFiniteSetBuild == OperEx(TlaFiniteSetOper.isFiniteSet, tla.name("a")))
    assert(isFiniteSetBuildBad2 == NullEx)

  }

  test("Test direct methods: TlaFunOper") {
    val appBuild = bd.appFun(tla.name("a"), tla.name("b")).untyped()

    assert(appBuild == OperEx(TlaFunOper.app, tla.name("a"), tla.name("b")))

    val domainBuild = bd.dom(tla.name("a")).untyped()

    assert(domainBuild == OperEx(TlaFunOper.domain, tla.name("a")))

    val enumBuild1 = bd.enumFun(tla.name("a"), tla.name("b")).untyped()
    val enumBuild2 = bd.enumFun(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(enumBuild1 == OperEx(TlaFunOper.rec, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.enumFun(tla.name("a"), tla.name("b"), tla.name("c")).untyped())
    assert(enumBuild2 == OperEx(TlaFunOper.rec, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assertThrows[IllegalArgumentException](bd.enumFun(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped())

    val exceptBuild1 = bd.except(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val exceptBuild2 = bd.except(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(exceptBuild1 == OperEx(TlaFunOper.except, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.except(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(exceptBuild2 == OperEx(TlaFunOper.except, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assertThrows[IllegalArgumentException](bd.except(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped())

    val funDefBuild1 = bd.funDef(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val funDefBuild2 = bd.funDef(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.funDef(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assertThrows[IllegalArgumentException](bd.funDef(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped())

    val tupleBuild1 = bd.tuple().untyped()
    val tupleBuild2 = bd.tuple(tla.name("a"), tla.name("b")).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, tla.name("a"), tla.name("b")))
  }

  test("Test byName: TlaFunOper") {
    val appBuild = bd.byName(TlaFunOper.app.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.app.name, tla.name("a")).untyped())
    assert(appBuild == OperEx(TlaFunOper.app, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.app.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val domainBuild = bd.byName(TlaFunOper.domain.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.domain.name).untyped())
    assert(domainBuild == OperEx(TlaFunOper.domain, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.domain.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val enumBuild1 = bd.byName(TlaFunOper.rec.name, tla.name("a"), tla.name("b")).untyped()
    val enumBuild2 = bd.byName(TlaFunOper.rec.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.rec.name, tla.name("a")).untyped())
    assert(enumBuild1 == OperEx(TlaFunOper.rec, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.rec.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())
    assert(enumBuild2 == OperEx(TlaFunOper.rec, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.rec.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped())

    val exceptBuild1 = bd.byName(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val exceptBuild2 = bd.byName(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, tla.name("a")).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, tla.name("a"), tla.name("b")).untyped())
    assert(exceptBuild1 == OperEx(TlaFunOper.except, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(exceptBuild2 == OperEx(TlaFunOper.except, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped())

    val funDefBuild1 = bd.byName(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val funDefBuild2 = bd.byName(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, tla.name("a")).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, tla.name("a"), tla.name("b")).untyped())
    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assertThrows[IllegalArgumentException](bd.byName(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped())

    val tupleBuild1 = bd.byName(TlaFunOper.tuple.name).untyped()
    val tupleBuild2 = bd.byName(TlaFunOper.tuple.name, tla.name("a"), tla.name("b")).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, tla.name("a"), tla.name("b")))

  }

  test("Test byNameOrNull: TlaFunOper") {
    val appBuildBad1 = bd.byNameOrNull(TlaFunOper.app.name, tla.name("a")).untyped()
    val appBuild = bd.byNameOrNull(TlaFunOper.app.name, tla.name("a"), tla.name("b")).untyped()
    val appBuildBad2 = bd.byNameOrNull(TlaFunOper.app.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(appBuildBad1 == NullEx)
    assert(appBuild == OperEx(TlaFunOper.app, tla.name("a"), tla.name("b")))
    assert(appBuildBad2 == NullEx)

    val domainBuildBad1 = bd.byNameOrNull(TlaFunOper.domain.name).untyped()
    val domainBuild = bd.byNameOrNull(TlaFunOper.domain.name, tla.name("a")).untyped()
    val domainBuildBad2 = bd.byNameOrNull(TlaFunOper.domain.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(domainBuildBad1 == NullEx)
    assert(domainBuild == OperEx(TlaFunOper.domain, tla.name("a")))
    assert(domainBuildBad2 == NullEx)

    val enumBuildEmpty = bd.byNameOrNull(TlaFunOper.rec.name).untyped()
    val enumBuild1 = bd.byNameOrNull(TlaFunOper.rec.name, tla.name("a"), tla.name("b")).untyped()
    val enumBuildBad1 = bd.byNameOrNull(TlaFunOper.rec.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val enumBuild2 = bd.byNameOrNull(TlaFunOper.rec.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val enumBuildBad2 = bd.byNameOrNull(TlaFunOper.rec.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(enumBuildEmpty == OperEx(TlaFunOper.rec))
    assert(enumBuild1 == OperEx(TlaFunOper.rec, tla.name("a"), tla.name("b")))
    assert(enumBuildBad1 == NullEx)
    assert(enumBuild2 == OperEx(TlaFunOper.rec, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assert(enumBuildBad2 == NullEx)

    val exceptBuildEmpty = bd.byNameOrNull(TlaFunOper.except.name).untyped()
    val exceptBuildSingle = bd.byNameOrNull(TlaFunOper.except.name, tla.name("a")).untyped()
    val exceptBuildBad1 = bd.byNameOrNull(TlaFunOper.except.name, tla.name("a"), tla.name("b")).untyped()
    val exceptBuild1 = bd.byNameOrNull(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val exceptBuildBad2 = bd.byNameOrNull(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val exceptBuild2 = bd.byNameOrNull(TlaFunOper.except.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(exceptBuildEmpty == NullEx)
    assert(exceptBuildSingle == NullEx)
    assert(exceptBuildBad1 == NullEx)
    assert(exceptBuild1 == OperEx(TlaFunOper.except, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(exceptBuildBad2 == NullEx)
    assert(exceptBuild2 == OperEx(TlaFunOper.except, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))

    val funDefBuildEmpty = bd.byNameOrNull(TlaFunOper.funDef.name).untyped()
    val funDefBuildSingle = bd.byNameOrNull(TlaFunOper.funDef.name, tla.name("a")).untyped()
    val funDefBuildBad1 = bd.byNameOrNull(TlaFunOper.funDef.name, tla.name("a"), tla.name("b")).untyped()
    val funDefBuild1 = bd.byNameOrNull(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val funDefBuildBad2 = bd.byNameOrNull(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val funDefBuild2 = bd.byNameOrNull(TlaFunOper.funDef.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(funDefBuildEmpty == NullEx)
    assert(funDefBuildSingle == NullEx)
    assert(funDefBuildBad1 == NullEx)
    assert(funDefBuild1 == OperEx(TlaFunOper.funDef, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(funDefBuildBad2 == NullEx)
    assert(funDefBuild2 == OperEx(TlaFunOper.funDef, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))

    val tupleBuild1 = bd.byNameOrNull(TlaFunOper.tuple.name).untyped()
    val tupleBuild2 = bd.byNameOrNull(TlaFunOper.tuple.name, tla.name("a"), tla.name("b")).untyped()

    assert(tupleBuild1 == OperEx(TlaFunOper.tuple))
    assert(tupleBuild2 == OperEx(TlaFunOper.tuple, tla.name("a"), tla.name("b")))
  }

  test("Test direct methods: TlaSeqOper") {
    val appendBuild = bd.append(tla.name("a"), tla.name("b")).untyped()

    assert(appendBuild == OperEx(TlaSeqOper.append, tla.name("a"), tla.name("b")))

    val concatBuild = bd.concat(tla.name("a"), tla.name("b")).untyped()

    assert(concatBuild == OperEx(TlaSeqOper.concat, tla.name("a"), tla.name("b")))

    val headBuild = bd.head(tla.name("a")).untyped()

    assert(headBuild == OperEx(TlaSeqOper.head, tla.name("a")))

    val tailBuild = bd.tail(tla.name("a")).untyped()

    assert(tailBuild == OperEx(TlaSeqOper.tail, tla.name("a")))

    val lenBuild = bd.len(tla.name("a")).untyped()

    assert(lenBuild == OperEx(TlaSeqOper.len, tla.name("a")))
  }

  test("Test byName: TlaSeqOper") {
    val appendBuild = bd.byName(TlaSeqOper.append.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.append.name, tla.name("a")).untyped())
    assert(appendBuild == OperEx(TlaSeqOper.append, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.append.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val concatBuild = bd.byName(TlaSeqOper.concat.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.concat.name, tla.name("a")).untyped())
    assert(concatBuild == OperEx(TlaSeqOper.concat, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.concat.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val headBuild = bd.byName(TlaSeqOper.head.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.head.name).untyped())
    assert(headBuild == OperEx(TlaSeqOper.head, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.head.name, tla.name("a"), tla.name("b")).untyped())

    val tailBuild = bd.byName(TlaSeqOper.tail.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.tail.name).untyped())
    assert(tailBuild == OperEx(TlaSeqOper.tail, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.tail.name, tla.name("a"), tla.name("b")).untyped())

    val lenBuild = bd.byName(TlaSeqOper.len.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.len.name).untyped())
    assert(lenBuild == OperEx(TlaSeqOper.len, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSeqOper.len.name, tla.name("a"), tla.name("b")).untyped())
  }

  test("Test byNameOrNull: TlaSeqOper") {
    val appendBuildBad1 = bd.byNameOrNull(TlaSeqOper.append.name, tla.name("a")).untyped()
    val appendBuild = bd.byNameOrNull(TlaSeqOper.append.name, tla.name("a"), tla.name("b")).untyped()
    val appendBuildBad2 = bd.byNameOrNull(TlaSeqOper.append.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(appendBuildBad1 == NullEx)
    assert(appendBuild == OperEx(TlaSeqOper.append, tla.name("a"), tla.name("b")))
    assert(appendBuildBad2 == NullEx)

    val concatBuildBad1 = bd.byNameOrNull(TlaSeqOper.concat.name, tla.name("a")).untyped()
    val concatBuild = bd.byNameOrNull(TlaSeqOper.concat.name, tla.name("a"), tla.name("b")).untyped()
    val concatBuildBad2 = bd.byNameOrNull(TlaSeqOper.concat.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(concatBuildBad1 == NullEx)
    assert(concatBuild == OperEx(TlaSeqOper.concat, tla.name("a"), tla.name("b")))
    assert(concatBuildBad2 == NullEx)

    val headBuildBad1 = bd.byNameOrNull(TlaSeqOper.head.name).untyped()
    val headBuild = bd.byNameOrNull(TlaSeqOper.head.name, tla.name("a")).untyped()
    val headBuildBad2 = bd.byNameOrNull(TlaSeqOper.head.name, tla.name("a"), tla.name("b")).untyped()

    assert(headBuildBad1 == NullEx)
    assert(headBuild == OperEx(TlaSeqOper.head, tla.name("a")))
    assert(headBuildBad2 == NullEx)

    val tailBuildBad1 = bd.byNameOrNull(TlaSeqOper.tail.name).untyped()
    val tailBuild = bd.byNameOrNull(TlaSeqOper.tail.name, tla.name("a")).untyped()
    val tailBuildBad2 = bd.byNameOrNull(TlaSeqOper.tail.name, tla.name("a"), tla.name("b")).untyped()

    assert(tailBuildBad1 == NullEx)
    assert(tailBuild == OperEx(TlaSeqOper.tail, tla.name("a")))
    assert(tailBuildBad2 == NullEx)

    val lenBuildBad1 = bd.byNameOrNull(TlaSeqOper.len.name).untyped()
    val lenBuild = bd.byNameOrNull(TlaSeqOper.len.name, tla.name("a")).untyped()
    val lenBuildBad2 = bd.byNameOrNull(TlaSeqOper.len.name, tla.name("a"), tla.name("b")).untyped()

    assert(lenBuildBad1 == NullEx)
    assert(lenBuild == OperEx(TlaSeqOper.len, tla.name("a")))
    assert(lenBuildBad2 == NullEx)
  }

  test("Test direct methods: TlaSetOper") {
    val enumSetBuild1 = bd.enumSet().untyped()
    val enumSetBuild2 = bd.enumSet(tla.name("a"), tla.name("b")).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, tla.name("a"), tla.name("b")))

    val inBuild = bd.in(tla.name("a"), tla.name("b")).untyped()

    assert(inBuild == OperEx(TlaSetOper.in, tla.name("a"), tla.name("b")))

    val notinBuild = bd.notin(tla.name("a"), tla.name("b")).untyped()

    assert(notinBuild == OperEx(TlaSetOper.notin, tla.name("a"), tla.name("b")))

    val capBuild = bd.cap(tla.name("a"), tla.name("b")).untyped()

    assert(capBuild == OperEx(TlaSetOper.cap, tla.name("a"), tla.name("b")))

    val cupBuild = bd.cup(tla.name("a"), tla.name("b")).untyped()

    assert(cupBuild == OperEx(TlaSetOper.cup, tla.name("a"), tla.name("b")))

    val unionBuild = bd.union(tla.name("a")).untyped()

    assert(unionBuild == OperEx(TlaSetOper.union, tla.name("a")))

    val filterBuild = bd.filter(tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(filterBuild == OperEx(TlaSetOper.filter, tla.name("a"), tla.name("b"), tla.name("c")))

    val mapBuild1 = bd.map(tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val mapBuild2 = bd.map(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(mapBuild1 == OperEx(TlaSetOper.map, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.map(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(mapBuild2 == OperEx(TlaSetOper.map, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))
    assertThrows[IllegalArgumentException](bd.map(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e"), tla.name("f")).untyped())

    val funSetBuild = bd.funSet(tla.name("a"), tla.name("b")).untyped()

    assert(funSetBuild == OperEx(TlaSetOper.funSet, tla.name("a"), tla.name("b")))

    val recSetBuild1 = bd.recSet(tla.name("a"), tla.name("b")).untyped()
    val recSetBuild2 = bd.recSet(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(recSetBuild1 == OperEx(TlaSetOper.recSet, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.recSet(tla.name("a"), tla.name("b"), tla.name("c")).untyped())
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assertThrows[IllegalArgumentException](bd.recSet(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped())

    val seqSetBuild = bd.seqSet(tla.name("a")).untyped()

    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, tla.name("a")))

    val subseteqBuild = bd.subseteq(tla.name("a"), tla.name("b")).untyped()
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, tla.name("a"), tla.name("b")))

    val setminusBuild = bd.setminus(tla.name("a"), tla.name("b")).untyped()

    assert(setminusBuild == OperEx(TlaSetOper.setminus, tla.name("a"), tla.name("b")))

    val timesBuild1 = bd.times(tla.name("a"), tla.name("b")).untyped()
    val timesBuild2 = bd.times(tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assertThrows[IllegalArgumentException](bd.times().untyped())
    assertThrows[IllegalArgumentException](bd.times(tla.name("a")).untyped())
    assert(timesBuild1 == OperEx(TlaSetOper.times, tla.name("a"), tla.name("b")))
    assert(timesBuild2 == OperEx(TlaSetOper.times, tla.name("a"), tla.name("b"), tla.name("c")))

    val powSetBuild = bd.powSet(tla.name("a")).untyped()

    assert(powSetBuild == OperEx(TlaSetOper.powerset, tla.name("a")))
  }

  test("Test byName: TlaSetOper") {
    val enumSetBuild1 = bd.byName(TlaSetOper.enumSet.name).untyped()
    val enumSetBuild2 = bd.byName(TlaSetOper.enumSet.name, tla.name("a"), tla.name("b")).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, tla.name("a"), tla.name("b")))

    val inBuild = bd.byName(TlaSetOper.in.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.in.name, tla.name("a")).untyped())
    assert(inBuild == OperEx(TlaSetOper.in, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.in.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val notinBuild = bd.byName(TlaSetOper.notin.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.notin.name, tla.name("a")).untyped())
    assert(notinBuild == OperEx(TlaSetOper.notin, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.notin.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val capBuild = bd.byName(TlaSetOper.cap.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cap.name, tla.name("a")).untyped())
    assert(capBuild == OperEx(TlaSetOper.cap, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cap.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val cupBuild = bd.byName(TlaSetOper.cup.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cup.name, tla.name("a")).untyped())
    assert(cupBuild == OperEx(TlaSetOper.cup, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.cup.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val unionBuild = bd.byName(TlaSetOper.union.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.union.name).untyped())
    assert(unionBuild == OperEx(TlaSetOper.union, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.union.name, tla.name("a"), tla.name("b")).untyped())

    val filterBuild = bd.byName(TlaSetOper.filter.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.filter.name, tla.name("a"), tla.name("b")).untyped())
    assert(filterBuild == OperEx(TlaSetOper.filter, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.filter.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())

    val mapBuild1 = bd.byNameOrNull(TlaSetOper.map.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val mapBuild2 = bd.byNameOrNull(TlaSetOper.map.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.map.name, tla.name("a"), tla.name("b")).untyped())
    assert(mapBuild1 == OperEx(TlaSetOper.map, tla.name("a"), tla.name("b"), tla.name("c")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.map.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped())
    assert(mapBuild2 == OperEx(TlaSetOper.map, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))

    val funSetBuild = bd.byName(TlaSetOper.funSet.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.funSet.name, tla.name("a")).untyped())
    assert(funSetBuild == OperEx(TlaSetOper.funSet, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.funSet.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val recSetBuild1 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a"), tla.name("b")).untyped()
    val recSetBuild2 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, tla.name("a")).untyped())
    assert(recSetBuild1 == OperEx(TlaSetOper.recSet, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.recSet.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped())

    val seqSetBuild = bd.byName(TlaSetOper.seqSet.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.seqSet.name).untyped())
    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.seqSet.name, tla.name("a"), tla.name("b")).untyped())

    val subseteqBuild = bd.byName(TlaSetOper.subseteq.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.subseteq.name, tla.name("a")).untyped())
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.subseteq.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val setminusBuild = bd.byName(TlaSetOper.setminus.name, tla.name("a"), tla.name("b")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.setminus.name, tla.name("a")).untyped())
    assert(setminusBuild == OperEx(TlaSetOper.setminus, tla.name("a"), tla.name("b")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.setminus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped())

    val timesBuild1 = bd.byName(TlaSetOper.times.name, tla.name("a"), tla.name("b")).untyped()
    val timesBuild2 = bd.byName(TlaSetOper.times.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.times.name).untyped())
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.times.name, tla.name("a")).untyped())
    assert(timesBuild1 == OperEx(TlaSetOper.times, tla.name("a"), tla.name("b")))
    assert(timesBuild2 == OperEx(TlaSetOper.times, tla.name("a"), tla.name("b"), tla.name("c")))

    val powSetBuild = bd.byName(TlaSetOper.powerset.name, tla.name("a")).untyped()

    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.powerset.name).untyped())
    assert(powSetBuild == OperEx(TlaSetOper.powerset, tla.name("a")))
    assertThrows[IllegalArgumentException](bd.byName(TlaSetOper.powerset.name, tla.name("a"), tla.name("b")).untyped())

  }

  test("Test byNameOrNull: TlaSetOper") {
    val enumSetBuild1 = bd.byNameOrNull(TlaSetOper.enumSet.name).untyped()
    val enumSetBuild2 = bd.byNameOrNull(TlaSetOper.enumSet.name, tla.name("a"), tla.name("b")).untyped()

    assert(enumSetBuild1 == OperEx(TlaSetOper.enumSet))
    assert(enumSetBuild2 == OperEx(TlaSetOper.enumSet, tla.name("a"), tla.name("b")))

    val inBuildBad1 = bd.byNameOrNull(TlaSetOper.in.name, tla.name("a")).untyped()
    val inBuild = bd.byNameOrNull(TlaSetOper.in.name, tla.name("a"), tla.name("b")).untyped()
    val inBuildBad2 = bd.byNameOrNull(TlaSetOper.in.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(inBuildBad1 == NullEx)
    assert(inBuild == OperEx(TlaSetOper.in, tla.name("a"), tla.name("b")))
    assert(inBuildBad2 == NullEx)

    val notinBuildBad1 = bd.byNameOrNull(TlaSetOper.notin.name, tla.name("a")).untyped()
    val notinBuild = bd.byNameOrNull(TlaSetOper.notin.name, tla.name("a"), tla.name("b")).untyped()
    val notinBuildBad2 = bd.byNameOrNull(TlaSetOper.notin.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(notinBuildBad1 == NullEx)
    assert(notinBuild == OperEx(TlaSetOper.notin, tla.name("a"), tla.name("b")))
    assert(notinBuildBad2 == NullEx)

    val capBuildBad1 = bd.byNameOrNull(TlaSetOper.cap.name, tla.name("a")).untyped()
    val capBuild = bd.byNameOrNull(TlaSetOper.cap.name, tla.name("a"), tla.name("b")).untyped()
    val capBuildBad2 = bd.byNameOrNull(TlaSetOper.cap.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(capBuildBad1 == NullEx)
    assert(capBuild == OperEx(TlaSetOper.cap, tla.name("a"), tla.name("b")))
    assert(capBuildBad2 == NullEx)

    val cupBuildBad1 = bd.byNameOrNull(TlaSetOper.cup.name, tla.name("a")).untyped()
    val cupBuild = bd.byNameOrNull(TlaSetOper.cup.name, tla.name("a"), tla.name("b")).untyped()
    val cupBuildBad2 = bd.byNameOrNull(TlaSetOper.cup.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(cupBuildBad1 == NullEx)
    assert(cupBuild == OperEx(TlaSetOper.cup, tla.name("a"), tla.name("b")))
    assert(cupBuildBad2 == NullEx)

    val unionBuildBad1 = bd.byNameOrNull(TlaSetOper.union.name).untyped()
    val unionBuild = bd.byNameOrNull(TlaSetOper.union.name, tla.name("a")).untyped()
    val unionBuildBad2 = bd.byNameOrNull(TlaSetOper.union.name, tla.name("a"), tla.name("b")).untyped()

    assert(unionBuildBad1 == NullEx)
    assert(unionBuild == OperEx(TlaSetOper.union, tla.name("a")))
    assert(unionBuildBad2 == NullEx)

    val filterBuildBad1 = bd.byNameOrNull(TlaSetOper.filter.name, tla.name("a"), tla.name("b")).untyped()
    val filterBuild = bd.byNameOrNull(TlaSetOper.filter.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val filterBuildBad2 = bd.byNameOrNull(TlaSetOper.filter.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()

    assert(filterBuildBad1 == NullEx)
    assert(filterBuild == OperEx(TlaSetOper.filter, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(filterBuildBad2 == NullEx)

    val mapBuildBad1 = bd.byNameOrNull(TlaSetOper.map.name, tla.name("a"), tla.name("b")).untyped()
    val mapBuild1 = bd.byNameOrNull(TlaSetOper.map.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val mapBuildBad2 = bd.byNameOrNull(TlaSetOper.map.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val mapBuild2 = bd.byNameOrNull(TlaSetOper.map.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(mapBuildBad1 == NullEx)
    assert(mapBuild1 == OperEx(TlaSetOper.map, tla.name("a"), tla.name("b"), tla.name("c")))
    assert(mapBuildBad2 == NullEx)
    assert(mapBuild2 == OperEx(TlaSetOper.map, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")))

    val funSetBuildBad1 = bd.byNameOrNull(TlaSetOper.funSet.name, tla.name("a")).untyped()
    val funSetBuild = bd.byNameOrNull(TlaSetOper.funSet.name, tla.name("a"), tla.name("b")).untyped()
    val funSetBuildBad2 = bd.byNameOrNull(TlaSetOper.funSet.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(funSetBuildBad1 == NullEx)
    assert(funSetBuild == OperEx(TlaSetOper.funSet, tla.name("a"), tla.name("b")))
    assert(funSetBuildBad2 == NullEx)

    val recSetBuildBad0 = bd.byNameOrNull(TlaSetOper.recSet.name).untyped()
    val recSetBuildBad1 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a")).untyped()
    val recSetBuild1 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a"), tla.name("b")).untyped()
    val recSetBuildBad2 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()
    val recSetBuild2 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")).untyped()
    val recSetBuildBad3 = bd.byNameOrNull(TlaSetOper.recSet.name, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d"), tla.name("e")).untyped()

    assert(recSetBuildBad0 == NullEx)
    assert(recSetBuildBad1 == NullEx)
    assert(recSetBuild1 == OperEx(TlaSetOper.recSet, tla.name("a"), tla.name("b")))
    assert(recSetBuildBad2 == NullEx)
    assert(recSetBuild2 == OperEx(TlaSetOper.recSet, tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")))
    assert(recSetBuildBad3 == NullEx)

    val seqSetBuildBad1 = bd.byNameOrNull(TlaSetOper.seqSet.name).untyped()
    val seqSetBuild = bd.byNameOrNull(TlaSetOper.seqSet.name, tla.name("a")).untyped()
    val seqSetBuildBad2 = bd.byNameOrNull(TlaSetOper.seqSet.name, tla.name("a"), tla.name("b")).untyped()

    assert(seqSetBuildBad1 == NullEx)
    assert(seqSetBuild == OperEx(TlaSetOper.seqSet, tla.name("a")))
    assert(seqSetBuildBad2 == NullEx)

    val subseteqBuildBad1 = bd.byNameOrNull(TlaSetOper.subseteq.name, tla.name("a")).untyped()
    val subseteqBuild = bd.byNameOrNull(TlaSetOper.subseteq.name, tla.name("a"), tla.name("b")).untyped()
    val subseteqBuildBad2 = bd.byNameOrNull(TlaSetOper.subseteq.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(subseteqBuildBad1 == NullEx)
    assert(subseteqBuild == OperEx(TlaSetOper.subseteq, tla.name("a"), tla.name("b")))
    assert(subseteqBuildBad2 == NullEx)

    val setminusBuildBad1 = bd.byNameOrNull(TlaSetOper.setminus.name, tla.name("a")).untyped()
    val setminusBuild = bd.byNameOrNull(TlaSetOper.setminus.name, tla.name("a"), tla.name("b")).untyped()
    val setminusBuildBad2 = bd.byNameOrNull(TlaSetOper.setminus.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(setminusBuildBad1 == NullEx)
    assert(setminusBuild == OperEx(TlaSetOper.setminus, tla.name("a"), tla.name("b")))
    assert(setminusBuildBad2 == NullEx)

    val timesBuildBad1 = bd.byNameOrNull(TlaSetOper.times.name).untyped()
    val timesBuildBad2 = bd.byNameOrNull(TlaSetOper.times.name, tla.name("a")).untyped()
    val timesBuild1 = bd.byNameOrNull(TlaSetOper.times.name, tla.name("a"), tla.name("b")).untyped()
    val timesBuild2 = bd.byNameOrNull(TlaSetOper.times.name, tla.name("a"), tla.name("b"), tla.name("c")).untyped()

    assert(timesBuildBad1 == NullEx)
    assert(timesBuildBad2 == NullEx)
    assert(timesBuild1 == OperEx(TlaSetOper.times, tla.name("a"), tla.name("b")))
    assert(timesBuild2 == OperEx(TlaSetOper.times, tla.name("a"), tla.name("b"), tla.name("c")))

    val powersetBuildBad1 = bd.byNameOrNull(TlaSetOper.powerset.name).untyped()
    val powersetBuild = bd.byNameOrNull(TlaSetOper.powerset.name, tla.name("a")).untyped()
    val powersetBuildBad2 = bd.byNameOrNull(TlaSetOper.powerset.name, tla.name("a"), tla.name("b")).untyped()

    assert(powersetBuildBad1 == NullEx)
    assert(powersetBuild == OperEx(TlaSetOper.powerset, tla.name("a")))
    assert(powersetBuildBad2 == NullEx)

  }
}

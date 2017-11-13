package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestBuilder extends FunSuite {

  /** reusable values */
  val n_a = NameEx("a")
  val n_b = NameEx("b")
  val n_c = NameEx("c")
  val n_d = NameEx("d")
  val n_e = NameEx("e")
  val n_f = NameEx("f")
  val n_g = NameEx("g")

  import at.forsyte.apalache.tla.lir.{Builder => bd}

  test("Test direct methods: Names and values"){
    val nameBuild = bd.mk_name( "a" )

    assert( nameBuild == NameEx( "a" ) )

    val vBigInt : BigInt = BigInt( "1000000015943534656464398536" )
    val vBigDecimal : BigDecimal = 1.111132454253626474876842798573504607
    val vBool = false
    val vString = "a string val"

    val biBuild   = bd.mk_value( vBigInt )
    val bdBuild   = bd.mk_value( vBigDecimal )
    val boolBuild = bd.mk_value( vBool )
    val strBuild  = bd.mk_value( vString )

    assert( biBuild   == ValEx( TlaInt( vBigInt ) ) )
    assert( bdBuild   == ValEx( TlaDecimal( vBigDecimal ) ) )
    assert( boolBuild == ValEx( TlaBool( vBool) ) )
    assert( strBuild  == ValEx( TlaStr( vString ) ) )
  }

  test("Test mk_operByName: bad calls"){
    assertThrows[NoSuchElementException]( bd.mk_operByName( "not an operator name", NullEx, n_b ) )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.plus.name, NullEx ) )
  }

  test("Test mk_operByNameOrNull: bad calls"){
    val nullBadName = bd.mk_operByNameOrNull( "not an operator name", NullEx, n_b )

    assert( nullBadName == NullEx )

    val nullBadArity = bd.mk_operByNameOrNull( TlaArithOper.plus.name, NullEx )

    assert( nullBadArity == NullEx )
  }

  test("Test direct methods: TlaOper"){
    val eqBuild1 = bd.mk_eq( n_a, n_b )
    val eqBuild2 = bd.mk_eq( n_a, 2 )

    assert( eqBuild1 == OperEx( TlaOper.eq, n_a, n_b ) )
    assert( eqBuild2 == OperEx( TlaOper.eq, n_a, ValEx( TlaInt( 2 ) ) ) )

    val neBuild1 = bd.mk_ne( n_a, n_b )
    val neBuild2 = bd.mk_ne( n_a, 2 )

    assert( neBuild1 == OperEx( TlaOper.ne, n_a, n_b ) )
    assert( neBuild2 == OperEx( TlaOper.ne, n_a, ValEx( TlaInt( 2 ) ) ) )

    val applyBuild1 = bd.mk_apply( n_a )
    val applyBuild2 = bd.mk_apply( n_a, n_b )
    val applyBuild3 = bd.mk_apply( n_a, n_b, n_c )
    val applyBuild4 = bd.mk_apply( n_a, n_b, n_c, n_d )

    assert( applyBuild1 == OperEx( TlaOper.apply, n_a ) )
    assert( applyBuild2 == OperEx( TlaOper.apply, n_a, n_b ) )
    assert( applyBuild3 == OperEx( TlaOper.apply, n_a, n_b, n_c ) )
    assert( applyBuild4 == OperEx( TlaOper.apply, n_a, n_b, n_c, n_d ) )

    val chooseBuild1 = bd.mk_choose( n_a, n_b )
    val chooseBuild2 = bd.mk_choose( n_a, n_b, n_c )

    assert( chooseBuild1 == OperEx( TlaOper.chooseUnbounded, n_a, n_b ) )
    assert( chooseBuild2 == OperEx( TlaOper.chooseBounded  , n_a, n_b, n_c ) )
  }

  test("Test mk_operByName: TlaOper"){
    val eqBuild = bd.mk_operByName( TlaOper.eq.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaOper.eq.name, n_a ) )
    assert( eqBuild == OperEx( TlaOper.eq, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaOper.eq.name, n_a, n_b, n_c ) )

    val neBuild = bd.mk_operByName( TlaOper.ne.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaOper.ne.name, n_a ) )
    assert( neBuild == OperEx( TlaOper.ne, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaOper.ne.name, n_a, n_b, n_c ) )

    val cbBuild = bd.mk_operByName( TlaOper.chooseBounded.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaOper.chooseBounded.name, n_a, n_b )
    )
    assert( cbBuild == OperEx( TlaOper.chooseBounded, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaOper.chooseBounded.name, n_a, n_b, n_c, n_d )
    )

    val cubBuild = bd.mk_operByName( TlaOper.chooseUnbounded.name, n_a, n_b )

    assert( cubBuild == OperEx( TlaOper.chooseUnbounded, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaOper.chooseUnbounded.name, n_a, n_b, n_c )
    )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaOper.chooseUnbounded.name, n_a, n_b, n_c, n_d )
    )
  }

  test("Test mk_operByNameOrNull: TlaOper"){
    val eqBuildBad1 = bd.mk_operByNameOrNull( TlaOper.eq.name, n_a )
    val eqBuild     = bd.mk_operByNameOrNull( TlaOper.eq.name, n_a, n_b )
    val eqBuildBad2 = bd.mk_operByNameOrNull( TlaOper.eq.name, n_a, n_b, n_c )

    assert( eqBuildBad1 == NullEx )
    assert( eqBuild     == OperEx( TlaOper.eq, n_a, n_b ) )
    assert( eqBuildBad2 == NullEx )

    val neBuildBad1 = bd.mk_operByNameOrNull( TlaOper.ne.name, n_a )
    val neBuild     = bd.mk_operByNameOrNull( TlaOper.ne.name, n_a, n_b )
    val neBuildBad2 = bd.mk_operByNameOrNull( TlaOper.ne.name, n_a, n_b, n_c )

    assert( neBuildBad1 == NullEx )
    assert( neBuild     == OperEx( TlaOper.ne, n_a, n_b ) )
    assert( neBuildBad2 == NullEx )

    val cbBuildBad1 = bd.mk_operByNameOrNull( TlaOper.chooseBounded.name, n_a, n_b )
    val cbBuild     = bd.mk_operByNameOrNull( TlaOper.chooseBounded.name, n_a, n_b, n_c )
    val cbBuildBad2 = bd.mk_operByNameOrNull( TlaOper.chooseBounded.name, n_a, n_b, n_c, n_d )

    assert( cbBuildBad1 == NullEx )
    assert( cbBuild     == OperEx( TlaOper.chooseBounded, n_a, n_b, n_c ) )
    assert( cbBuildBad2 == NullEx )

    val cubBuild     = bd.mk_operByNameOrNull( TlaOper.chooseUnbounded.name, n_a, n_b )
    val cubBuildBad1 = bd.mk_operByNameOrNull( TlaOper.chooseUnbounded.name, n_a, n_b, n_c )
    val cubBuildBad2 = bd.mk_operByNameOrNull( TlaOper.chooseUnbounded.name, n_a, n_b, n_c, n_d )

    assert( cubBuild     == OperEx( TlaOper.chooseUnbounded, n_a, n_b ) )
    assert( cubBuildBad1 == NullEx )
    assert( cubBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaBoolOper "){
    val andBuild1 = bd.mk_and( n_a )
    val andBuild2 = bd.mk_and( n_a, n_b )
    val andBuild3 = bd.mk_and( n_a, n_b, n_c )
    val andBuild4 = bd.mk_and( n_a, n_b, n_c, n_d )

    assert( andBuild1 == OperEx( TlaBoolOper.and, n_a ) )
    assert( andBuild2 == OperEx( TlaBoolOper.and, n_a, n_b ) )
    assert( andBuild3 == OperEx( TlaBoolOper.and, n_a, n_b, n_c ) )
    assert( andBuild4 == OperEx( TlaBoolOper.and, n_a, n_b, n_c, n_d ) )

    val orBuild1 = bd.mk_or( n_a )
    val orBuild2 = bd.mk_or( n_a, n_b )
    val orBuild3 = bd.mk_or( n_a, n_b, n_c )
    val orBuild4 = bd.mk_or( n_a, n_b, n_c, n_d )

    assert( orBuild1 == OperEx( TlaBoolOper.or, n_a ) )
    assert( orBuild2 == OperEx( TlaBoolOper.or, n_a, n_b ) )
    assert( orBuild3 == OperEx( TlaBoolOper.or, n_a, n_b, n_c ) )
    assert( orBuild4 == OperEx( TlaBoolOper.or, n_a, n_b, n_c, n_d ) )

    val notBuild1 = bd.mk_not( n_a )

    assert( notBuild1 == OperEx( TlaBoolOper.not, n_a ) )

    val impliesBuild1 = bd.mk_implies( n_a, n_b )

    assert( impliesBuild1 == OperEx( TlaBoolOper.implies, n_a, n_b ) )

    val equivBuild1 = bd.mk_equiv( n_a, n_b )

    assert( equivBuild1 == OperEx( TlaBoolOper.equiv, n_a, n_b ) )

    val forallBuild1 = bd.mk_forall( n_a, n_b )
    val forallBuild2 = bd.mk_forall( n_a, n_b, n_c )

    assert( forallBuild1 == OperEx( TlaBoolOper.forallUnbounded, n_a, n_b ) )
    assert( forallBuild2 == OperEx( TlaBoolOper.forall         , n_a, n_b, n_c ) )

    val existsBuild1 = bd.mk_exists( n_a, n_b )
    val existsBuild2 = bd.mk_exists( n_a, n_b, n_c )

    assert( existsBuild1 == OperEx( TlaBoolOper.existsUnbounded, n_a, n_b ) )
    assert( existsBuild2 == OperEx( TlaBoolOper.exists         , n_a, n_b, n_c ) )
  }

  test("Test mk_operByName: TlaBoolOper "){
    val andBuild1 = bd.mk_operByName( TlaBoolOper.and.name )
    val andBuild2 = bd.mk_operByName( TlaBoolOper.and.name, n_a )
    val andBuild3 = bd.mk_operByName( TlaBoolOper.and.name, n_a, n_b )

    assert( andBuild1 == OperEx( TlaBoolOper.and ) )
    assert( andBuild2 == OperEx( TlaBoolOper.and, n_a ) )
    assert( andBuild3 == OperEx( TlaBoolOper.and, n_a, n_b ) )

    val orBuild1 = bd.mk_operByName( TlaBoolOper.or.name )
    val orBuild2 = bd.mk_operByName( TlaBoolOper.or.name, n_a )
    val orBuild3 = bd.mk_operByName( TlaBoolOper.or.name, n_a, n_b )

    assert( orBuild1 == OperEx( TlaBoolOper.or ) )
    assert( orBuild2 == OperEx( TlaBoolOper.or, n_a ) )
    assert( orBuild3 == OperEx( TlaBoolOper.or, n_a, n_b ) )

    val notBuild = bd.mk_operByName( TlaBoolOper.not.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaBoolOper.not.name ) )
    assert( notBuild == OperEx( TlaBoolOper.not, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaBoolOper.not.name, n_a, n_b ) )

    val impliesBuild = bd.mk_operByName( TlaBoolOper.implies.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaBoolOper.implies.name, n_a ) )
    assert( impliesBuild == OperEx( TlaBoolOper.implies, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaBoolOper.implies.name, n_a, n_b, n_c )
    )

  }

  test("Test mk_operByNameOrNull: TlaBoolOper "){
    val andBuild1 = bd.mk_operByNameOrNull( TlaBoolOper.and.name )
    val andBuild2 = bd.mk_operByNameOrNull( TlaBoolOper.and.name, n_a )
    val andBuild3 = bd.mk_operByNameOrNull( TlaBoolOper.and.name, n_a, n_b )

    assert( andBuild1 == OperEx( TlaBoolOper.and ) )
    assert( andBuild2 == OperEx( TlaBoolOper.and, n_a ) )
    assert( andBuild3 == OperEx( TlaBoolOper.and, n_a, n_b ) )

    val orBuild1 = bd.mk_operByNameOrNull( TlaBoolOper.or.name )
    val orBuild2 = bd.mk_operByNameOrNull( TlaBoolOper.or.name, n_a )
    val orBuild3 = bd.mk_operByNameOrNull( TlaBoolOper.or.name, n_a, n_b )

    assert( orBuild1 == OperEx( TlaBoolOper.or ) )
    assert( orBuild2 == OperEx( TlaBoolOper.or, n_a ) )
    assert( orBuild3 == OperEx( TlaBoolOper.or, n_a, n_b ) )

    val notBuildBad1 = bd.mk_operByNameOrNull( TlaBoolOper.not.name )
    val notBuild     = bd.mk_operByNameOrNull( TlaBoolOper.not.name, n_a )
    val notBuildBad2 = bd.mk_operByNameOrNull( TlaBoolOper.not.name, n_a, n_b )

    assert( notBuildBad1 == NullEx )
    assert( notBuild     == OperEx( TlaBoolOper.not, n_a ) )
    assert( notBuildBad2 == NullEx )

    val impliesBuildBad1 = bd.mk_operByNameOrNull( TlaBoolOper.implies.name, n_a )
    val impliesBuild     = bd.mk_operByNameOrNull( TlaBoolOper.implies.name, n_a, n_b )
    val impliesBuildBad2 = bd.mk_operByNameOrNull( TlaBoolOper.implies.name, n_a, n_b, n_c )

    assert( impliesBuildBad1 == NullEx )
    assert( impliesBuild == OperEx( TlaBoolOper.implies, n_a, n_b ) )
    assert( impliesBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaActionOper"){
    val primeBuild1 = bd.mk_prime( n_a )
    val primeBuild2 = bd.mk_prime( "name" )

    assert( primeBuild1 == OperEx( TlaActionOper.prime, n_a ) )
    assert( primeBuild2 == OperEx( TlaActionOper.prime, NameEx( "name" ) ) )

    val prime_eqBuild1 = bd.mk_prime_eq( "name", n_a )
    val prime_eqBuild2 = bd.mk_prime_eq( n_a, n_b )
    val prime_eqBuild3 = bd.mk_prime_eq( "name", 1 )
    val prime_eqBuild4 = bd.mk_prime_eq( n_a, 2 )

    assert(
      prime_eqBuild1 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( "name" ) ), n_a )
    )
    assert(
      prime_eqBuild2 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, n_a ), n_b )
    )
    assert(
      prime_eqBuild3 == OperEx(
        TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( "name" ) ), ValEx( TlaInt( 1 ) )
      )
    )
    assert(
      prime_eqBuild4 == OperEx(
        TlaOper.eq, OperEx( TlaActionOper.prime, n_a ), ValEx( TlaInt( 2 ) )
      )
    )

    val stutterBuild = bd.mk_stutter( n_a, n_b )

    assert( stutterBuild == OperEx( TlaActionOper.stutter, n_a, n_b ) )
    
    val nostutterBuild = bd.mk_nostutter( n_a, n_b )

    assert( nostutterBuild == OperEx( TlaActionOper.nostutter, n_a, n_b ) )

    val enabledBuild = bd.mk_enabled( n_a )

    assert( enabledBuild == OperEx( TlaActionOper.enabled, n_a ) )

    val unchangedBuild = bd.mk_unchanged( n_a )

    assert( unchangedBuild == OperEx( TlaActionOper.unchanged, n_a ) )

    val compositionBuild = bd.mk_composition( n_a, n_b )

    assert( compositionBuild == OperEx( TlaActionOper.composition, n_a, n_b ) )

  }

  test("Test mk_operByName: TlaActionOper"){
    val primeBuild = bd.mk_operByNameOrNull( TlaActionOper.prime.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaActionOper.prime.name ) )
    assert( primeBuild == OperEx( TlaActionOper.prime, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.prime.name, n_a, n_b )
    )

    val stutterBuild = bd.mk_operByName( TlaActionOper.stutter.name, n_a, n_b )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.stutter.name, n_a )
    )
    assert( stutterBuild == OperEx( TlaActionOper.stutter, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.stutter.name, n_a, n_b, n_c )
    )

    val nostutterBuild = bd.mk_operByName( TlaActionOper.nostutter.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaActionOper.nostutter.name, n_a ) )
    assert( nostutterBuild == OperEx( TlaActionOper.nostutter, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.nostutter.name, n_a, n_b, n_c )
    )

    val enabledBuild = bd.mk_operByName( TlaActionOper.enabled.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaActionOper.enabled.name ) )
    assert( enabledBuild == OperEx( TlaActionOper.enabled, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.enabled.name, n_a, n_b )
    )

    val unchangedBuild = bd.mk_operByName( TlaActionOper.unchanged.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaActionOper.unchanged.name ) )
    assert( unchangedBuild == OperEx( TlaActionOper.unchanged, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.unchanged.name, n_a, n_b )
    )

    val compositionBuild = bd.mk_operByName( TlaActionOper.composition.name, n_a, n_b )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.composition.name, n_a )
    )
    assert( compositionBuild == OperEx( TlaActionOper.composition, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaActionOper.composition.name, n_a, n_b, n_c )
    )
  }

  test("Test mk_operByNameOrNull: TlaActionOper"){
    val primeBuildBad1 = bd.mk_operByNameOrNull( TlaActionOper.prime.name )
    val primeBuild     = bd.mk_operByNameOrNull( TlaActionOper.prime.name, n_a )
    val primeBuildBad2 = bd.mk_operByNameOrNull( TlaActionOper.prime.name, n_a, n_b )

    assert( primeBuildBad1 == NullEx )
    assert( primeBuild     == OperEx( TlaActionOper.prime, n_a ) )
    assert( primeBuildBad2 == NullEx )

    val stutterBuildBad1 = bd.mk_operByNameOrNull( TlaActionOper.stutter.name, n_a )
    val stutterBuild     = bd.mk_operByNameOrNull( TlaActionOper.stutter.name, n_a, n_b )
    val stutterBuildBad2 = bd.mk_operByNameOrNull( TlaActionOper.stutter.name, n_a, n_b, n_c )

    assert( stutterBuildBad1 == NullEx )
    assert( stutterBuild     == OperEx( TlaActionOper.stutter, n_a, n_b ) )
    assert( stutterBuildBad2 == NullEx )

    val nostutterBuildBad1 = bd.mk_operByNameOrNull( TlaActionOper.nostutter.name, n_a )
    val nostutterBuild     = bd.mk_operByNameOrNull( TlaActionOper.nostutter.name, n_a, n_b )
    val nostutterBuildBad2 = bd.mk_operByNameOrNull( TlaActionOper.nostutter.name, n_a, n_b, n_c )

    assert( nostutterBuildBad1 == NullEx )
    assert( nostutterBuild     == OperEx( TlaActionOper.nostutter, n_a, n_b ) )
    assert( nostutterBuildBad2 == NullEx )

    val enabledBuildBad1 = bd.mk_operByNameOrNull( TlaActionOper.enabled.name )
    val enabledBuild     = bd.mk_operByNameOrNull( TlaActionOper.enabled.name, n_a )
    val enabledBuildBad2 = bd.mk_operByNameOrNull( TlaActionOper.enabled.name, n_a, n_b )

    assert( enabledBuildBad1 == NullEx )
    assert( enabledBuild     == OperEx( TlaActionOper.enabled, n_a ) )
    assert( enabledBuildBad2 == NullEx )

    val unchangedBuildBad1 = bd.mk_operByNameOrNull( TlaActionOper.unchanged.name )
    val unchangedBuild     = bd.mk_operByNameOrNull( TlaActionOper.unchanged.name, n_a )
    val unchangedBuildBad2 = bd.mk_operByNameOrNull( TlaActionOper.unchanged.name, n_a, n_b )

    assert( unchangedBuildBad1 == NullEx )
    assert( unchangedBuild     == OperEx( TlaActionOper.unchanged, n_a ) )
    assert( unchangedBuildBad2 == NullEx )

    val compositionBuildBad1 = bd.mk_operByNameOrNull( TlaActionOper.composition.name, n_a )
    val compositionBuild     = bd.mk_operByNameOrNull( TlaActionOper.composition.name, n_a, n_b )
    val compositionBuildBad2 = bd.mk_operByNameOrNull(
      TlaActionOper.composition.name, n_a, n_b, n_c
    )

    assert( compositionBuildBad1 == NullEx )
    assert( compositionBuild     == OperEx( TlaActionOper.composition, n_a, n_b ) )
    assert( compositionBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaControlOper"){

    val caseBuild1 = bd.mk_case( n_a, n_b )
    val caseBuild2 = bd.mk_case( n_a, n_b, n_c )
    val caseBuild3 = bd.mk_case( n_a, n_b, n_c, n_d )
    val caseBuild4 = bd.mk_case( n_a, n_b, n_c, n_d, n_e )
    val caseBuild5 = bd.mk_case( n_a, n_b, n_c, n_d, n_e, n_f )
    val caseBuild6 = bd.mk_case( n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assert( caseBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assert( caseBuild4 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assert( caseBuild5 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert(
      caseBuild6 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g )
    )

    val caseSplitBuild1 = bd.mk_caseSplit( n_a, n_b )
    val caseSplitBuild2 = bd.mk_caseSplit( n_a, n_b, n_c, n_d )
    val caseSplitBuild3 = bd.mk_caseSplit( n_a, n_b, n_c, n_d, n_e, n_f )

    assert( caseSplitBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_caseSplit( n_a, n_b, n_c ) )
    assert( caseSplitBuild2 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assertThrows[IllegalArgumentException]( bd.mk_caseSplit( n_a, n_b, n_c, n_d, n_e ) )
    assert( caseSplitBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )

    val caseOtherBuild1 = bd.mk_caseOther( n_a, n_b, n_c )
    val caseOtherBuild2 = bd.mk_caseOther( n_a, n_b, n_c, n_d, n_e )
    val caseOtherBuild3 = bd.mk_caseOther( n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseOtherBuild1 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.mk_caseOther( n_a, n_b, n_c, n_d ) )
    assert( caseOtherBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.mk_caseOther( n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert(
      caseOtherBuild3 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g )
    )

    val iteBuild1 = bd.mk_ite( n_a, n_b, n_c )

    assert( iteBuild1 == OperEx( TlaControlOper.ifThenElse, n_a, n_b, n_c ) )

  }

  test("Test mk_operByName: TlaControlOper"){
    val caseBuild1 = bd.mk_operByName( TlaControlOper.caseNoOther.name, n_a, n_b )
    val caseBuild2 = bd.mk_operByName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )
    val caseBuild3 = bd.mk_operByName( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d )
    val caseBuild4 =
      bd.mk_operByName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e )
    val caseBuild5 =
      bd.mk_operByName( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d, n_e, n_f )
    val caseBuild6 =
      bd.mk_operByName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assert( caseBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assert( caseBuild4 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assert( caseBuild5 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert(
      caseBuild6 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g )
    )

    val caseNoOtherBuild = bd.mk_operByName( TlaControlOper.caseNoOther.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaControlOper.caseNoOther.name ) )
    assert( caseNoOtherBuild == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaControlOper.caseNoOther.name, n_a, n_b, n_c )
    )

    val caseWithOtherBuild = bd.mk_operByName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaControlOper.caseWithOther.name ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaControlOper.caseWithOther.name, n_a )
    )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaControlOper.caseWithOther.name, n_a, n_b )
    )
    assert( caseWithOtherBuild == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )

    val iteBuild = bd.mk_operByName(TlaControlOper.ifThenElse.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName(TlaControlOper.ifThenElse.name, n_a, n_b )
    )
    assert( iteBuild == OperEx( TlaControlOper.ifThenElse, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName(TlaControlOper.ifThenElse.name, n_a, n_b, n_c, n_d )
    )
  }

  test("Test mk_operByNameOrNull: TlaControlOper") {
    val caseBuild1 = bd.mk_operByNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b )
    val caseBuild2 = bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )
    val caseBuild3 = bd.mk_operByNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d )
    val caseBuild4 =
      bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e )
    val caseBuild5 =
      bd.mk_operByNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d, n_e, n_f )
    val caseBuild6 =
      bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assert( caseBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assert( caseBuild4 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assert( caseBuild5 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert(
      caseBuild6 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g )
    )

    val caseNoOtherBuildEmpty = bd.mk_operByNameOrNull( TlaControlOper.caseNoOther.name )
    val caseNoOtherBuild      = bd.mk_operByNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b )
    val caseNoOtherBuildBad   =
      bd.mk_operByNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b, n_c )

    assert( caseNoOtherBuildEmpty == NullEx )
    assert( caseNoOtherBuild      == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseNoOtherBuildBad   == NullEx )

    val caseWithOtherBuildEmpty  = bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name )
    val caseWithOtherBuildSingle = bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name, n_a )
    val caseWithOtherBuildBad    =
      bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b )
    val caseWithOtherBuild       =
      bd.mk_operByNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )

    assert( caseWithOtherBuildEmpty  == NullEx )
    assert( caseWithOtherBuildSingle == NullEx )
    assert( caseWithOtherBuildBad    == NullEx )
    assert( caseWithOtherBuild       == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )

    val iteBuildBad1 = bd.mk_operByNameOrNull(TlaControlOper.ifThenElse.name, n_a, n_b )
    val iteBuild     = bd.mk_operByNameOrNull(TlaControlOper.ifThenElse.name, n_a, n_b, n_c )
    val iteBuildBad2 = bd.mk_operByNameOrNull(TlaControlOper.ifThenElse.name, n_a, n_b, n_c, n_d )

    assert( iteBuildBad1 == NullEx )
    assert( iteBuild     == OperEx( TlaControlOper.ifThenElse, n_a, n_b, n_c ) )
    assert( iteBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaTempOper"){
    val AABuild = bd.mk_AA( n_a, n_b )

    assert( AABuild == OperEx( TlaTempOper.AA, n_a, n_b ) )

    val EEBuild = bd.mk_EE( n_a, n_b )

    assert( EEBuild == OperEx( TlaTempOper.EE, n_a, n_b ) )

    val boxBuild = bd.mk_box( n_a )

    assert( boxBuild == OperEx( TlaTempOper.box, n_a ) )

    val diamondBuild = bd.mk_diamond( n_a )

    assert( diamondBuild == OperEx( TlaTempOper.diamond, n_a ) )

    val leadsToBuild = bd.mk_leadsTo( n_a, n_b )

    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, n_a, n_b ) )

    val guaranteesBuild = bd.mk_guarantees( n_a, n_b )

    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, n_a, n_b ) )

    val strongFairnessBuild = bd.mk_SF( n_a, n_b )

    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, n_a, n_b ) )

    val weakFairnessBuild = bd.mk_WF( n_a, n_b )

    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, n_a, n_b ) )
  }

  test("Test mk_operByName: TlaTempOper"){
    val AABuild = bd.mk_operByName( TlaTempOper.AA.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName(TlaTempOper.AA.name, n_a ) )
    assert( AABuild == OperEx( TlaTempOper.AA, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName(TlaTempOper.AA.name, n_a, n_b, n_c )
    )

    val EEBuild = bd.mk_operByName( TlaTempOper.EE.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaTempOper.EE.name, n_a ) )
    assert( EEBuild == OperEx( TlaTempOper.EE, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.EE.name, n_a, n_b, n_c )
    )

    val boxBuild = bd.mk_operByName( TlaTempOper.box.name, n_a )

    assertThrows[IllegalArgumentException](  bd.mk_operByName( TlaTempOper.box.name ) )
    assert( boxBuild == OperEx( TlaTempOper.box, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.box.name, n_a, n_b )
    )

    val diamondBuild = bd.mk_operByName( TlaTempOper.diamond.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaTempOper.diamond.name ) )
    assert( diamondBuild == OperEx( TlaTempOper.diamond, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.diamond.name, n_a, n_b )
    )

    val leadsToBuild = bd.mk_operByName( TlaTempOper.leadsTo.name, n_a, n_b )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.leadsTo.name, n_a )
    )
    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.leadsTo.name, n_a, n_b, n_c )
    )

    val guaranteesBuild = bd.mk_operByName( TlaTempOper.guarantees.name, n_a, n_b )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.guarantees.name, n_a )
    )
    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.guarantees.name, n_a, n_b, n_c )
    )

    val strongFairnessBuild = bd.mk_operByName( TlaTempOper.strongFairness.name, n_a, n_b )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.strongFairness.name, n_a )
    )
    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.strongFairness.name, n_a, n_b, n_c )
    )

    val weakFairnessBuild = bd.mk_operByName( TlaTempOper.weakFairness.name, n_a, n_b )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.weakFairness.name, n_a )
    )
    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaTempOper.weakFairness.name, n_a, n_b, n_c )
    )

  }

  test("Test mk_operByNameOrNull: TlaTempOper"){
    val AABuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.AA.name, n_a )
    val AABuild     = bd.mk_operByNameOrNull( TlaTempOper.AA.name, n_a, n_b )
    val AABuildBad2 = bd.mk_operByNameOrNull( TlaTempOper.AA.name, n_a, n_b, n_c )

    assert( AABuildBad1 == NullEx )
    assert( AABuild     == OperEx( TlaTempOper.AA, n_a, n_b ) )
    assert( AABuildBad2 == NullEx )

    val EEBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.EE.name, n_a )
    val EEBuild     = bd.mk_operByNameOrNull( TlaTempOper.EE.name, n_a, n_b )
    val EEBuildBad2 = bd.mk_operByNameOrNull( TlaTempOper.EE.name, n_a, n_b, n_c )

    assert( EEBuildBad1 == NullEx )
    assert( EEBuild     == OperEx( TlaTempOper.EE, n_a, n_b ) )
    assert( EEBuildBad2 == NullEx )

    val boxBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.box.name )
    val boxBuild     = bd.mk_operByNameOrNull( TlaTempOper.box.name, n_a )
    val boxBuildBad2 = bd.mk_operByNameOrNull( TlaTempOper.box.name, n_a, n_b )

    assert( boxBuildBad1 == NullEx )
    assert( boxBuild     == OperEx( TlaTempOper.box, n_a ) )
    assert( boxBuildBad2 == NullEx )

    val diamondBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.diamond.name )
    val diamondBuild     = bd.mk_operByNameOrNull( TlaTempOper.diamond.name, n_a )
    val diamondBuildBad2 = bd.mk_operByNameOrNull( TlaTempOper.diamond.name, n_a, n_b )

    assert( diamondBuildBad1 == NullEx )
    assert( diamondBuild     == OperEx( TlaTempOper.diamond, n_a ) )
    assert( diamondBuildBad2 == NullEx )

    val leadsToBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.leadsTo.name, n_a )
    val leadsToBuild     = bd.mk_operByNameOrNull( TlaTempOper.leadsTo.name, n_a, n_b )
    val leadsToBuildBad2 = bd.mk_operByNameOrNull( TlaTempOper.leadsTo.name, n_a, n_b, n_c )

    assert( leadsToBuildBad1 == NullEx )
    assert( leadsToBuild     == OperEx( TlaTempOper.leadsTo, n_a, n_b ) )
    assert( leadsToBuildBad2 == NullEx )

    val guaranteesBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.guarantees.name, n_a )
    val guaranteesBuild     = bd.mk_operByNameOrNull( TlaTempOper.guarantees.name, n_a, n_b )
    val guaranteesBuildBad2 = bd.mk_operByNameOrNull( TlaTempOper.guarantees.name, n_a, n_b, n_c )

    assert( guaranteesBuildBad1 == NullEx )
    assert( guaranteesBuild     == OperEx( TlaTempOper.guarantees, n_a, n_b ) )
    assert( guaranteesBuildBad2 == NullEx )

    val strongFairnessBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.strongFairness.name, n_a )
    val strongFairnessBuild     =
      bd.mk_operByNameOrNull( TlaTempOper.strongFairness.name, n_a, n_b )
    val strongFairnessBuildBad2 =
      bd.mk_operByNameOrNull( TlaTempOper.strongFairness.name, n_a, n_b, n_c )

    assert( strongFairnessBuildBad1 == NullEx )
    assert( strongFairnessBuild     == OperEx( TlaTempOper.strongFairness, n_a, n_b ) )
    assert( strongFairnessBuildBad2 == NullEx )

    val weakFairnessBuildBad1 = bd.mk_operByNameOrNull( TlaTempOper.weakFairness.name, n_a )
    val weakFairnessBuild     = bd.mk_operByNameOrNull( TlaTempOper.weakFairness.name, n_a, n_b )
    val weakFairnessBuildBad2 =
      bd.mk_operByNameOrNull( TlaTempOper.weakFairness.name, n_a, n_b, n_c )

    assert( weakFairnessBuildBad1 == NullEx )
    assert( weakFairnessBuild     == OperEx( TlaTempOper.weakFairness, n_a, n_b ) )
    assert( weakFairnessBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaArithOper"){
    val sumBuild1 = bd.mk_sum()
    val sumBuild2 = bd.mk_sum( n_a, n_b )

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, n_a, n_b ) )

    val plusBuild1 = bd.mk_plus( n_a, n_b )
    val plusBuild2 = bd.mk_plus( n_a, 2 )
    val plusBuild3 = bd.mk_plus( 1  , n_b )
    val plusBuild4 = bd.mk_plus( 1  , 2 )

    assert( plusBuild1 == OperEx( TlaArithOper.plus, n_a                 , n_b ) )
    assert( plusBuild2 == OperEx( TlaArithOper.plus, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( plusBuild3 == OperEx( TlaArithOper.plus, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( plusBuild4 == OperEx( TlaArithOper.plus, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val minusBuild1 = bd.mk_minus( n_a, n_b )
    val minusBuild2 = bd.mk_minus( n_a, 2 )
    val minusBuild3 = bd.mk_minus( 1  , n_b )
    val minusBuild4 = bd.mk_minus( 1  , 2 )

    assert( minusBuild1 == OperEx( TlaArithOper.minus, n_a, n_b ) )
    assert( minusBuild2 == OperEx( TlaArithOper.minus, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( minusBuild3 == OperEx( TlaArithOper.minus, ValEx( TlaInt( 1 ) ), n_b ) )
    assert(
      minusBuild4 == OperEx( TlaArithOper.minus, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) )
    )

    val uminusBuild = bd.mk_uminus( n_a )

    assert( uminusBuild == OperEx( TlaArithOper.uminus, n_a ) )

    val prodBuild1 = bd.mk_prod()
    val prodBuild2 = bd.mk_prod( n_a, n_b )

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, n_a, n_b ) )

    val multBuild1 = bd.mk_mult( n_a, n_b )
    val multBuild2 = bd.mk_mult( n_a, 2 )
    val multBuild3 = bd.mk_mult( 1  , n_b )
    val multBuild4 = bd.mk_mult( 1  , 2 )

    assert( multBuild1 == OperEx( TlaArithOper.mult, n_a                 , n_b ) )
    assert( multBuild2 == OperEx( TlaArithOper.mult, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( multBuild3 == OperEx( TlaArithOper.mult, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( multBuild4 == OperEx( TlaArithOper.mult, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val divBuild1 = bd.mk_div( n_a, n_b )
    val divBuild2 = bd.mk_div( n_a, 2 )
    val divBuild3 = bd.mk_div( 1  , n_b )
    val divBuild4 = bd.mk_div( 1  , 2 )

    assert( divBuild1 == OperEx( TlaArithOper.div, n_a                 , n_b ) )
    assert( divBuild2 == OperEx( TlaArithOper.div, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( divBuild3 == OperEx( TlaArithOper.div, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( divBuild4 == OperEx( TlaArithOper.div, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val modBuild1 = bd.mk_mod( n_a, n_b )
    val modBuild2 = bd.mk_mod( n_a, 2 )
    val modBuild3 = bd.mk_mod( 1  , n_b )
    val modBuild4 = bd.mk_mod( 1  , 2 )

    assert( modBuild1 == OperEx( TlaArithOper.mod, n_a                 , n_b ) )
    assert( modBuild2 == OperEx( TlaArithOper.mod, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( modBuild3 == OperEx( TlaArithOper.mod, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( modBuild4 == OperEx( TlaArithOper.mod, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val realDivBuild1 = bd.mk_realDiv( n_a, n_b )
    val realDivBuild2 = bd.mk_realDiv( n_a, 2 )
    val realDivBuild3 = bd.mk_realDiv( 1  , n_b )
    val realDivBuild4 = bd.mk_realDiv( 1  , 2 )

    assert( realDivBuild1 == OperEx( TlaArithOper.realDiv, n_a, n_b ) )
    assert( realDivBuild2 == OperEx( TlaArithOper.realDiv, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( realDivBuild3 == OperEx( TlaArithOper.realDiv, ValEx( TlaInt( 1 ) ), n_b ) )
    assert(
      realDivBuild4 == OperEx( TlaArithOper.realDiv, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) )
    )

    val expBuild1 = bd.mk_exp( n_a, n_b )
    val expBuild2 = bd.mk_exp( n_a, 2 )
    val expBuild3 = bd.mk_exp( 1  , n_b )
    val expBuild4 = bd.mk_exp( 1  , 2 )

    assert( expBuild1 == OperEx( TlaArithOper.exp, n_a                 , n_b ) )
    assert( expBuild2 == OperEx( TlaArithOper.exp, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( expBuild3 == OperEx( TlaArithOper.exp, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( expBuild4 == OperEx( TlaArithOper.exp, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val dotdotBuild1 = bd.mk_dotdot( n_a, n_b )
    val dotdotBuild2 = bd.mk_dotdot( n_a, 2 )
    val dotdotBuild3 = bd.mk_dotdot( 1  , n_b )
    val dotdotBuild4 = bd.mk_dotdot( 1  , 2 )

    assert( dotdotBuild1 == OperEx( TlaArithOper.dotdot, n_a, n_b ) )
    assert( dotdotBuild2 == OperEx( TlaArithOper.dotdot, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( dotdotBuild3 == OperEx( TlaArithOper.dotdot, ValEx( TlaInt( 1 ) ), n_b ) )
    assert(
      dotdotBuild4 == OperEx( TlaArithOper.dotdot, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) )
    )

    val ltBuild1 = bd.mk_lt( n_a, n_b )
    val ltBuild2 = bd.mk_lt( n_a, 2 )
    val ltBuild3 = bd.mk_lt( 1  , n_b )
    val ltBuild4 = bd.mk_lt( 1  , 2 )

    assert( ltBuild1 == OperEx( TlaArithOper.lt, n_a                 , n_b ) )
    assert( ltBuild2 == OperEx( TlaArithOper.lt, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( ltBuild3 == OperEx( TlaArithOper.lt, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( ltBuild4 == OperEx( TlaArithOper.lt, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val gtBuild1 = bd.mk_gt( n_a, n_b )
    val gtBuild2 = bd.mk_gt( n_a, 2 )
    val gtBuild3 = bd.mk_gt( 1  , n_b )
    val gtBuild4 = bd.mk_gt( 1  , 2 )

    assert( gtBuild1 == OperEx( TlaArithOper.gt, n_a                 , n_b ) )
    assert( gtBuild2 == OperEx( TlaArithOper.gt, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( gtBuild3 == OperEx( TlaArithOper.gt, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( gtBuild4 == OperEx( TlaArithOper.gt, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val leBuild1 = bd.mk_le( n_a, n_b )
    val leBuild2 = bd.mk_le( n_a, 2 )
    val leBuild3 = bd.mk_le( 1  , n_b )
    val leBuild4 = bd.mk_le( 1  , 2 )

    assert( leBuild1 == OperEx( TlaArithOper.le, n_a                 , n_b ) )
    assert( leBuild2 == OperEx( TlaArithOper.le, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( leBuild3 == OperEx( TlaArithOper.le, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( leBuild4 == OperEx( TlaArithOper.le, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val geBuild1 = bd.mk_ge( n_a, n_b )
    val geBuild2 = bd.mk_ge( n_a, 2 )
    val geBuild3 = bd.mk_ge( 1  , n_b )
    val geBuild4 = bd.mk_ge( 1  , 2 )

    assert( geBuild1 == OperEx( TlaArithOper.ge, n_a                 , n_b ) )
    assert( geBuild2 == OperEx( TlaArithOper.ge, n_a                 , ValEx( TlaInt( 2 ) ) ) )
    assert( geBuild3 == OperEx( TlaArithOper.ge, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( geBuild4 == OperEx( TlaArithOper.ge, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )
  }

  test("Test mk_operByName: TlaArithOper"){
    val sumBuild1 = bd.mk_operByName( TlaArithOper.sum.name )
    val sumBuild2 = bd.mk_operByName( TlaArithOper.sum.name, n_a, n_b )

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, n_a, n_b ) )

    val plusBuild = bd.mk_operByName( TlaArithOper.plus.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.plus.name, n_a ) )
    assert( plusBuild == OperEx( TlaArithOper.plus, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaArithOper.plus.name, n_a, n_b, n_c )
    )

    val minusBuild = bd.mk_operByName( TlaArithOper.minus.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.minus.name, n_a ) )
    assert( minusBuild == OperEx( TlaArithOper.minus, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.minus.name, n_a, n_b, n_c )
    )

    val uminusBuild = bd.mk_operByName( TlaArithOper.uminus.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.uminus.name ) )
    assert( uminusBuild == OperEx( TlaArithOper.uminus, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaArithOper.uminus.name, n_a, n_b, n_c )
    )

    val prodBuild1 = bd.mk_operByName( TlaArithOper.prod.name )
    val prodBuild2 = bd.mk_operByName( TlaArithOper.prod.name, n_a, n_b )

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, n_a, n_b ) )

    val multBuild = bd.mk_operByName( TlaArithOper.mult.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.mult.name, n_a ) )
    assert( multBuild == OperEx( TlaArithOper.mult, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.mult.name, n_a, n_b, n_c )
    )
    
    val divBuild = bd.mk_operByName( TlaArithOper.div.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.div.name, n_a ) )
    assert( divBuild == OperEx( TlaArithOper.div, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.div.name, n_a, n_b, n_c )
    )

    val modBuild = bd.mk_operByName( TlaArithOper.mod.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.mod.name, n_a ) )
    assert( modBuild == OperEx( TlaArithOper.mod, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.mod.name, n_a, n_b, n_c )
    )

    val realDivBuild = bd.mk_operByName( TlaArithOper.realDiv.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.realDiv.name, n_a ) )
    assert( realDivBuild == OperEx( TlaArithOper.realDiv, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.realDiv.name, n_a, n_b, n_c )
    )
    
    val expBuild = bd.mk_operByName( TlaArithOper.exp.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.exp.name, n_a ) )
    assert( expBuild == OperEx( TlaArithOper.exp, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.exp.name, n_a, n_b, n_c )
    )

    val dotdotBuild = bd.mk_operByName( TlaArithOper.dotdot.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.dotdot.name, n_a ) )
    assert( dotdotBuild == OperEx( TlaArithOper.dotdot, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.dotdot.name, n_a, n_b, n_c )
    )

    val ltBuild = bd.mk_operByName( TlaArithOper.lt.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.lt.name, n_a ) )
    assert( ltBuild == OperEx( TlaArithOper.lt, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.lt.name, n_a, n_b, n_c )
    )

    val gtBuild = bd.mk_operByName( TlaArithOper.gt.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.gt.name, n_a ) )
    assert( gtBuild == OperEx( TlaArithOper.gt, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.gt.name, n_a, n_b, n_c )
    )

    val leBuild = bd.mk_operByName( TlaArithOper.le.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.le.name, n_a ) )
    assert( leBuild == OperEx( TlaArithOper.le, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.le.name, n_a, n_b, n_c )
    )

    val geBuild = bd.mk_operByName( TlaArithOper.ge.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaArithOper.ge.name, n_a ) )
    assert( geBuild == OperEx( TlaArithOper.ge, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaArithOper.ge.name, n_a, n_b, n_c )
    )
  }

  test("Test mk_operByNameOrNull: TlaArithOper"){
    val sumBuild1 = bd.mk_operByNameOrNull( TlaArithOper.sum.name )
    val sumBuild2 = bd.mk_operByNameOrNull( TlaArithOper.sum.name, n_a, n_b )

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, n_a, n_b ) )

    val plusBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.plus.name, n_a )
    val plusBuild     = bd.mk_operByNameOrNull( TlaArithOper.plus.name, n_a, n_b )
    val plusBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.plus.name, n_a, n_b, n_c )

    assert( plusBuildBad1 == NullEx )
    assert( plusBuild     == OperEx( TlaArithOper.plus, n_a, n_b ) )
    assert( plusBuildBad2 == NullEx )

    val minusBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.minus.name, n_a )
    val minusBuild     = bd.mk_operByNameOrNull( TlaArithOper.minus.name, n_a, n_b )
    val minusBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.minus.name, n_a, n_b, n_c )

    assert( minusBuildBad1 == NullEx )
    assert( minusBuild     == OperEx( TlaArithOper.minus, n_a, n_b ) )
    assert( minusBuildBad2 == NullEx )

    val uminusBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.uminus.name )
    val uminusBuild     = bd.mk_operByNameOrNull( TlaArithOper.uminus.name, n_a )
    val uminusBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.uminus.name, n_a, n_b, n_c )

    assert( uminusBuildBad1 == NullEx )
    assert( uminusBuild     == OperEx( TlaArithOper.uminus, n_a ) )
    assert( uminusBuildBad2 == NullEx )

    val prodBuild1 = bd.mk_operByNameOrNull( TlaArithOper.prod.name )
    val prodBuild2 = bd.mk_operByNameOrNull( TlaArithOper.prod.name, n_a, n_b )

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, n_a, n_b ) )

    val multBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.mult.name, n_a )
    val multBuild     = bd.mk_operByNameOrNull( TlaArithOper.mult.name, n_a, n_b )
    val multBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.mult.name, n_a, n_b, n_c )

    assert( multBuildBad1 == NullEx )
    assert( multBuild     == OperEx( TlaArithOper.mult, n_a, n_b ) )
    assert( multBuildBad2 == NullEx )

    val divBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.div.name, n_a )
    val divBuild     = bd.mk_operByNameOrNull( TlaArithOper.div.name, n_a, n_b )
    val divBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.div.name, n_a, n_b, n_c )

    assert( divBuildBad1 == NullEx )
    assert( divBuild     == OperEx( TlaArithOper.div, n_a, n_b ) )
    assert( divBuildBad2 == NullEx )

    val modBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.mod.name, n_a )
    val modBuild     = bd.mk_operByNameOrNull( TlaArithOper.mod.name, n_a, n_b )
    val modBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.mod.name, n_a, n_b, n_c )

    assert( modBuildBad1 == NullEx )
    assert( modBuild     == OperEx( TlaArithOper.mod, n_a, n_b ) )
    assert( modBuildBad2 == NullEx )

    val realDivBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.realDiv.name, n_a )
    val realDivBuild     = bd.mk_operByNameOrNull( TlaArithOper.realDiv.name, n_a, n_b )
    val realDivBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.realDiv.name, n_a, n_b, n_c )

    assert( realDivBuildBad1 == NullEx )
    assert( realDivBuild     == OperEx( TlaArithOper.realDiv, n_a, n_b ) )
    assert( realDivBuildBad2 == NullEx )

    val expBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.exp.name, n_a )
    val expBuild     = bd.mk_operByNameOrNull( TlaArithOper.exp.name, n_a, n_b )
    val expBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.exp.name, n_a, n_b, n_c )

    assert( expBuildBad1 == NullEx )
    assert( expBuild     == OperEx( TlaArithOper.exp, n_a, n_b ) )
    assert( expBuildBad2 == NullEx )

    val dotdotBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.dotdot.name, n_a )
    val dotdotBuild     = bd.mk_operByNameOrNull( TlaArithOper.dotdot.name, n_a, n_b )
    val dotdotBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.dotdot.name, n_a, n_b, n_c )

    assert( dotdotBuildBad1 == NullEx )
    assert( dotdotBuild     == OperEx( TlaArithOper.dotdot, n_a, n_b ) )
    assert( dotdotBuildBad2 == NullEx )

    val ltBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.lt.name, n_a )
    val ltBuild     = bd.mk_operByNameOrNull( TlaArithOper.lt.name, n_a, n_b )
    val ltBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.lt.name, n_a, n_b, n_c )

    assert( ltBuildBad1 == NullEx )
    assert( ltBuild     == OperEx( TlaArithOper.lt, n_a, n_b ) )
    assert( ltBuildBad2 == NullEx )

    val gtBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.gt.name, n_a )
    val gtBuild     = bd.mk_operByNameOrNull( TlaArithOper.gt.name, n_a, n_b )
    val gtBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.gt.name, n_a, n_b, n_c )

    assert( gtBuildBad1 == NullEx )
    assert( gtBuild     == OperEx( TlaArithOper.gt, n_a, n_b ) )
    assert( gtBuildBad2 == NullEx )

    val leBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.le.name, n_a )
    val leBuild     = bd.mk_operByNameOrNull( TlaArithOper.le.name, n_a, n_b )
    val leBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.le.name, n_a, n_b, n_c )

    assert( leBuildBad1 == NullEx )
    assert( leBuild     == OperEx( TlaArithOper.le, n_a, n_b ) )
    assert( leBuildBad2 == NullEx )

    val geBuildBad1 = bd.mk_operByNameOrNull( TlaArithOper.ge.name, n_a )
    val geBuild     = bd.mk_operByNameOrNull( TlaArithOper.ge.name, n_a, n_b )
    val geBuildBad2 = bd.mk_operByNameOrNull( TlaArithOper.ge.name, n_a, n_b, n_c )

    assert( geBuildBad1 == NullEx )
    assert( geBuild     == OperEx( TlaArithOper.ge, n_a, n_b ) )
    assert( geBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaFiniteSetOper"){
    val cardinalityBuild = bd.mk_card( n_a )

    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, n_a ) )

    val isFiniteSetBuild = bd.mk_isFin( n_a )

    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, n_a ) )
  }

  test("Test mk_operByName: TlaFiniteSetOper"){
    val cardinalityBuild = bd.mk_operByName( TlaFiniteSetOper.cardinality.name, n_a )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFiniteSetOper.cardinality.name )
    )
    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFiniteSetOper.cardinality.name, n_a, n_b, n_c )
    )

    val isFiniteSetBuild = bd.mk_operByName( TlaFiniteSetOper.isFiniteSet.name, n_a )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFiniteSetOper.isFiniteSet.name )
    )
    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFiniteSetOper.isFiniteSet.name, n_a, n_b, n_c )
    )
  }

  test("Test mk_operByNameOrNull: TlaFiniteSetOper"){
    val cardinalityBuildBad1 = bd.mk_operByNameOrNull( TlaFiniteSetOper.cardinality.name )
    val cardinalityBuild     = bd.mk_operByNameOrNull( TlaFiniteSetOper.cardinality.name, n_a )
    val cardinalityBuildBad2 =
      bd.mk_operByNameOrNull( TlaFiniteSetOper.cardinality.name, n_a, n_b, n_c )

    assert( cardinalityBuildBad1 == NullEx )
    assert( cardinalityBuild     == OperEx( TlaFiniteSetOper.cardinality, n_a ) )
    assert( cardinalityBuildBad2 == NullEx )

    val isFiniteSetBuildBad1 = bd.mk_operByNameOrNull( TlaFiniteSetOper.isFiniteSet.name )
    val isFiniteSetBuild     = bd.mk_operByNameOrNull( TlaFiniteSetOper.isFiniteSet.name, n_a )
    val isFiniteSetBuildBad2 =
      bd.mk_operByNameOrNull( TlaFiniteSetOper.isFiniteSet.name, n_a, n_b, n_c )

    assert( isFiniteSetBuildBad1 == NullEx )
    assert( isFiniteSetBuild     == OperEx( TlaFiniteSetOper.isFiniteSet, n_a ) )
    assert( isFiniteSetBuildBad2 == NullEx )

  }

  test("Test direct methods: TlaFunOper"){
    val appBuild = bd.mk_app( n_a, n_b )

    assert( appBuild == OperEx( TlaFunOper.app, n_a, n_b ) )

    val domainBuild = bd.mk_dom( n_a )

    assert( domainBuild == OperEx( TlaFunOper.domain, n_a ) )

    val enumBuild1 = bd.mk_enum( n_a, n_b )
    val enumBuild2 = bd.mk_enum( n_a, n_b, n_c, n_d )

    assert( enumBuild1 == OperEx( TlaFunOper.enum, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_enum( n_a, n_b, n_c )
    )
    assert( enumBuild2 == OperEx( TlaFunOper.enum, n_a, n_b, n_c, n_d ) )
    assertThrows[IllegalArgumentException](
      bd.mk_enum( n_a, n_b, n_c, n_d, n_e )
    )

    val exceptBuild1 = bd.mk_except( n_a, n_b, n_c )
    val exceptBuild2 = bd.mk_except( n_a, n_b, n_c, n_d, n_e )

    assert(exceptBuild1 == OperEx( TlaFunOper.except, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_except( n_a, n_b, n_c, n_d )
    )
    assert(exceptBuild2 == OperEx( TlaFunOper.except, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException](
      bd.mk_except( n_a, n_b, n_c, n_d, n_e, n_f )
    )

    val funDefBuild1 = bd.mk_funDef( n_a, n_b, n_c )
    val funDefBuild2 = bd.mk_funDef( n_a, n_b, n_c, n_d, n_e )

    assert(funDefBuild1 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_funDef( n_a, n_b, n_c, n_d )
    )
    assert(funDefBuild2 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException](
      bd.mk_funDef( n_a, n_b, n_c, n_d, n_e, n_f )
    )

    val tupleBuild1 = bd.mk_tuple()
    val tupleBuild2 = bd.mk_tuple( n_a, n_b )

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, n_a, n_b ) )
  }

  test("Test mk_operByName: TlaFunOper"){
    val appBuild = bd.mk_operByName( TlaFunOper.app.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.app.name, n_a ) )
    assert( appBuild == OperEx( TlaFunOper.app, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.app.name, n_a, n_b, n_c ) )

    val domainBuild = bd.mk_operByName( TlaFunOper.domain.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.domain.name ) )
    assert( domainBuild == OperEx( TlaFunOper.domain, n_a ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.domain.name, n_a, n_b, n_c )
    )

    val enumBuild1 = bd.mk_operByName( TlaFunOper.enum.name, n_a, n_b )
    val enumBuild2 = bd.mk_operByName( TlaFunOper.enum.name, n_a, n_b, n_c, n_d )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.enum.name ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.enum.name, n_a ) )
    assert( enumBuild1 == OperEx( TlaFunOper.enum, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.enum.name, n_a, n_b, n_c )
    )
    assert( enumBuild2 == OperEx( TlaFunOper.enum, n_a, n_b, n_c, n_d ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.enum.name, n_a, n_b, n_c, n_d, n_e )
    )

    val exceptBuild1 = bd.mk_operByName( TlaFunOper.except.name, n_a, n_b, n_c )
    val exceptBuild2 = bd.mk_operByName( TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.except.name ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.except.name, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.except.name, n_a, n_b ) )
    assert(exceptBuild1 == OperEx( TlaFunOper.except, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.except.name, n_a, n_b, n_c, n_d )
    )
    assert(exceptBuild2 == OperEx( TlaFunOper.except, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e, n_f )
    )

    val funDefBuild1 = bd.mk_operByName( TlaFunOper.funDef.name, n_a, n_b, n_c )
    val funDefBuild2 = bd.mk_operByName( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.funDef.name ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.funDef.name, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaFunOper.funDef.name, n_a, n_b ) )
    assert(funDefBuild1 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d )
    )
    assert(funDefBuild2 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e, n_f )
    )

    val tupleBuild1 = bd.mk_operByName( TlaFunOper.tuple.name )
    val tupleBuild2 = bd.mk_operByName( TlaFunOper.tuple.name, n_a, n_b )

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, n_a, n_b ) )

  }

  test("Test mk_operByNameOrNull: TlaFunOper"){
    val appBuildBad1 = bd.mk_operByNameOrNull( TlaFunOper.app.name, n_a )
    val appBuild     = bd.mk_operByNameOrNull( TlaFunOper.app.name, n_a, n_b )
    val appBuildBad2 = bd.mk_operByNameOrNull( TlaFunOper.app.name, n_a, n_b, n_c )

    assert( appBuildBad1 == NullEx )
    assert( appBuild     == OperEx( TlaFunOper.app, n_a, n_b ) )
    assert( appBuildBad2 == NullEx )

    val domainBuildBad1 = bd.mk_operByNameOrNull( TlaFunOper.domain.name )
    val domainBuild     = bd.mk_operByNameOrNull( TlaFunOper.domain.name, n_a )
    val domainBuildBad2 = bd.mk_operByNameOrNull( TlaFunOper.domain.name, n_a, n_b, n_c )

    assert( domainBuildBad1 == NullEx )
    assert( domainBuild == OperEx( TlaFunOper.domain, n_a ) )
    assert( domainBuildBad2 == NullEx )

    val enumBuildEmpty = bd.mk_operByNameOrNull( TlaFunOper.enum.name )
    val enumBuild1     = bd.mk_operByNameOrNull( TlaFunOper.enum.name, n_a, n_b )
    val enumBuildBad1  = bd.mk_operByNameOrNull( TlaFunOper.enum.name, n_a, n_b, n_c )
    val enumBuild2     = bd.mk_operByNameOrNull( TlaFunOper.enum.name, n_a, n_b, n_c, n_d )
    val enumBuildBad2  = bd.mk_operByNameOrNull( TlaFunOper.enum.name, n_a, n_b, n_c, n_d, n_e )

    assert( enumBuildEmpty == NullEx )
    assert( enumBuild1     == OperEx( TlaFunOper.enum, n_a, n_b ) )
    assert( enumBuildBad1  == NullEx )
    assert( enumBuild2     == OperEx( TlaFunOper.enum, n_a, n_b, n_c, n_d ) )
    assert( enumBuildBad2  == NullEx )

    val exceptBuildEmpty  = bd.mk_operByNameOrNull( TlaFunOper.except.name )
    val exceptBuildSingle = bd.mk_operByNameOrNull( TlaFunOper.except.name, n_a )
    val exceptBuildBad1   = bd.mk_operByNameOrNull( TlaFunOper.except.name, n_a, n_b )
    val exceptBuild1      = bd.mk_operByNameOrNull( TlaFunOper.except.name, n_a, n_b, n_c )
    val exceptBuildBad2   = bd.mk_operByNameOrNull( TlaFunOper.except.name, n_a, n_b, n_c, n_d )
    val exceptBuild2      =
      bd.mk_operByNameOrNull( TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e )

    assert(exceptBuildEmpty  == NullEx )
    assert(exceptBuildSingle == NullEx )
    assert(exceptBuildBad1   == NullEx )
    assert(exceptBuild1      == OperEx( TlaFunOper.except, n_a, n_b, n_c ) )
    assert(exceptBuildBad2   == NullEx )
    assert(exceptBuild2      == OperEx( TlaFunOper.except, n_a, n_b, n_c, n_d, n_e ) )

    val funDefBuildEmpty  = bd.mk_operByNameOrNull( TlaFunOper.funDef.name )
    val funDefBuildSingle = bd.mk_operByNameOrNull( TlaFunOper.funDef.name, n_a )
    val funDefBuildBad1   = bd.mk_operByNameOrNull( TlaFunOper.funDef.name, n_a, n_b )
    val funDefBuild1      = bd.mk_operByNameOrNull( TlaFunOper.funDef.name, n_a, n_b, n_c )
    val funDefBuildBad2   = bd.mk_operByNameOrNull( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d )
    val funDefBuild2      =
      bd.mk_operByNameOrNull( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e )

    assert(funDefBuildEmpty  == NullEx )
    assert(funDefBuildSingle == NullEx )
    assert(funDefBuildBad1   == NullEx )
    assert(funDefBuild1      == OperEx( TlaFunOper.funDef, n_a, n_b, n_c ) )
    assert(funDefBuildBad2   == NullEx )
    assert(funDefBuild2      == OperEx( TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e ) )

    val tupleBuild1 = bd.mk_operByNameOrNull( TlaFunOper.tuple.name )
    val tupleBuild2 = bd.mk_operByNameOrNull( TlaFunOper.tuple.name, n_a, n_b )

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, n_a, n_b ) )
  }

  test("Test direct methods: TlaSeqOper"){
    val appendBuild = bd.mk_append( n_a, n_b )

    assert( appendBuild == OperEx( TlaSeqOper.append, n_a, n_b ) )

    val concatBuild = bd.mk_concat( n_a, n_b )

    assert( concatBuild == OperEx( TlaSeqOper.concat, n_a, n_b ) )

    val headBuild = bd.mk_head( n_a )

    assert( headBuild == OperEx( TlaSeqOper.head, n_a ) )

    val tailBuild = bd.mk_tail( n_a )

    assert( tailBuild == OperEx( TlaSeqOper.tail, n_a ) )

    val lenBuild = bd.mk_len( n_a )

    assert( lenBuild == OperEx( TlaSeqOper.len, n_a ) )
  }

  test("Test mk_operByName: TlaSeqOper"){
    val appendBuild = bd.mk_operByName( TlaSeqOper.append.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.append.name, n_a ) )
    assert( appendBuild == OperEx( TlaSeqOper.append, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSeqOper.append.name, n_a, n_b, n_c )
    )

    val concatBuild = bd.mk_operByName( TlaSeqOper.concat.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.concat.name, n_a ) )
    assert( concatBuild == OperEx( TlaSeqOper.concat, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSeqOper.concat.name, n_a, n_b, n_c )
    )

    val headBuild = bd.mk_operByName( TlaSeqOper.head.name, n_a )
    
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.head.name ) )
    assert( headBuild == OperEx( TlaSeqOper.head, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.head.name, n_a, n_b ) )

    val tailBuild = bd.mk_operByName( TlaSeqOper.tail.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.tail.name ) )
    assert( tailBuild == OperEx( TlaSeqOper.tail, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.tail.name, n_a, n_b ) )

    val lenBuild = bd.mk_operByName( TlaSeqOper.len.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.len.name ) )
    assert( lenBuild == OperEx( TlaSeqOper.len, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSeqOper.len.name, n_a, n_b ) )
  }

  test("Test mk_operByNameOrNull: TlaSeqOper"){
    val appendBuildBad1 = bd.mk_operByNameOrNull( TlaSeqOper.append.name, n_a )
    val appendBuild     = bd.mk_operByNameOrNull( TlaSeqOper.append.name, n_a, n_b )
    val appendBuildBad2 = bd.mk_operByNameOrNull( TlaSeqOper.append.name, n_a, n_b, n_c )

    assert( appendBuildBad1 == NullEx )
    assert( appendBuild     == OperEx( TlaSeqOper.append, n_a, n_b ) )
    assert( appendBuildBad2 == NullEx )

    val concatBuildBad1 = bd.mk_operByNameOrNull( TlaSeqOper.concat.name, n_a )
    val concatBuild     = bd.mk_operByNameOrNull( TlaSeqOper.concat.name, n_a, n_b )
    val concatBuildBad2 = bd.mk_operByNameOrNull( TlaSeqOper.concat.name, n_a, n_b, n_c )

    assert( concatBuildBad1 == NullEx )
    assert( concatBuild     == OperEx( TlaSeqOper.concat, n_a, n_b ) )
    assert( concatBuildBad2 == NullEx )

    val headBuildBad1 = bd.mk_operByNameOrNull( TlaSeqOper.head.name )
    val headBuild     = bd.mk_operByNameOrNull( TlaSeqOper.head.name, n_a )
    val headBuildBad2 = bd.mk_operByNameOrNull( TlaSeqOper.head.name, n_a, n_b )

    assert( headBuildBad1 == NullEx )
    assert( headBuild     == OperEx( TlaSeqOper.head, n_a ) )
    assert( headBuildBad2 == NullEx )

    val tailBuildBad1 = bd.mk_operByNameOrNull( TlaSeqOper.tail.name )
    val tailBuild     = bd.mk_operByNameOrNull( TlaSeqOper.tail.name, n_a )
    val tailBuildBad2 = bd.mk_operByNameOrNull( TlaSeqOper.tail.name, n_a, n_b )

    assert( tailBuildBad1 == NullEx )
    assert( tailBuild     == OperEx( TlaSeqOper.tail, n_a ) )
    assert( tailBuildBad2 == NullEx )

    val lenBuildBad1 = bd.mk_operByNameOrNull( TlaSeqOper.len.name )
    val lenBuild     = bd.mk_operByNameOrNull( TlaSeqOper.len.name, n_a )
    val lenBuildBad2 = bd.mk_operByNameOrNull( TlaSeqOper.len.name, n_a, n_b )

    assert( lenBuildBad1 == NullEx )
    assert( lenBuild     == OperEx( TlaSeqOper.len, n_a ) )
    assert( lenBuildBad2 == NullEx )
  }

  test("Test direct methods: TlaSetOper"){
    val enumSetBuild1 = bd.mk_enumSet()
    val enumSetBuild2 = bd.mk_enumSet( n_a, n_b )

    assert( enumSetBuild1 == OperEx( TlaSetOper.enumSet ) )
    assert( enumSetBuild2 == OperEx( TlaSetOper.enumSet, n_a, n_b ) )

    val inBuild = bd.mk_in( n_a, n_b )

    assert( inBuild == OperEx( TlaSetOper.in, n_a, n_b ) )

    val notinBuild = bd.mk_notin( n_a, n_b )

    assert( notinBuild == OperEx( TlaSetOper.notin, n_a, n_b ) )

    val capBuild = bd.mk_cap( n_a, n_b )

    assert( capBuild == OperEx( TlaSetOper.cap, n_a, n_b ) )

    val cupBuild = bd.mk_cup( n_a, n_b )

    assert( cupBuild == OperEx( TlaSetOper.cup, n_a, n_b ) )

    val unionBuild = bd.mk_union( n_a )

    assert( unionBuild == OperEx( TlaSetOper.union, n_a ) )

    val filterBuild = bd.mk_filter( n_a, n_b, n_c )

    assert( filterBuild == OperEx( TlaSetOper.filter, n_a, n_b, n_c ) )

    val mapBuild1 = bd.mk_map( n_a, n_b, n_c )
    val mapBuild2 = bd.mk_map( n_a, n_b, n_c, n_d, n_e )

    assert( mapBuild1 == OperEx( TlaSetOper.map, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.mk_map( n_a, n_b, n_c, n_d ) )
    assert( mapBuild2 == OperEx( TlaSetOper.map, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.mk_map( n_a, n_b, n_c, n_d, n_e, n_f ) )

    val funSetBuild = bd.mk_funSet( n_a, n_b )

    assert( funSetBuild == OperEx( TlaSetOper.funSet, n_a, n_b ) )

    val recSetBuild1 = bd.mk_recSet()
    val recSetBuild2 = bd.mk_recSet( n_a, n_b )

    assert( recSetBuild1 == OperEx( TlaSetOper.recSet ) )
    assertThrows[IllegalArgumentException]( bd.mk_recSet( n_a ) )
    assert( recSetBuild2 == OperEx( TlaSetOper.recSet, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_recSet( n_a, n_b, n_c ) )

    val seqSetBuild = bd.mk_seqSet( n_a )

    assert( seqSetBuild == OperEx( TlaSetOper.seqSet, n_a ) )

    val subsetBuild = bd.mk_subset( n_a, n_b )

    assert( subsetBuild == OperEx( TlaSetOper.subsetProper, n_a, n_b ) )

    val subseteqBuild = bd.mk_subseteq( n_a, n_b )

    assert( subseteqBuild == OperEx( TlaSetOper.subseteq, n_a, n_b ) )

    val supsetBuild = bd.mk_supset( n_a, n_b )

    assert( supsetBuild == OperEx( TlaSetOper.supsetProper, n_a, n_b ) )

    val supseteqBuild = bd.mk_supseteq( n_a, n_b )

    assert( supseteqBuild == OperEx( TlaSetOper.supseteq, n_a, n_b ) )

    val setminusBuild = bd.mk_setminus( n_a, n_b )

    assert( setminusBuild == OperEx( TlaSetOper.setminus, n_a, n_b ) )

    val timesBuild1 = bd.mk_times( )
    val timesBuild2 = bd.mk_times( n_a, n_b )

    assert( timesBuild1 == OperEx( TlaSetOper.times ) )
    assert( timesBuild2 == OperEx( TlaSetOper.times, n_a, n_b ) )

    val powSetBuild = bd.mk_powSet( n_a )

    assert( powSetBuild == OperEx( TlaSetOper.powerset, n_a ) )
  }

  test("Test mk_operByName: TlaSetOper"){
    val enumSetBuild1 = bd.mk_operByName( TlaSetOper.enumSet.name )
    val enumSetBuild2 = bd.mk_operByName( TlaSetOper.enumSet.name, n_a, n_b )

    assert( enumSetBuild1 == OperEx( TlaSetOper.enumSet ) )
    assert( enumSetBuild2 == OperEx( TlaSetOper.enumSet, n_a, n_b ) )

    val inBuild = bd.mk_operByName( TlaSetOper.in.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.in.name, n_a ) )
    assert( inBuild == OperEx( TlaSetOper.in, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.in.name, n_a, n_b, n_c ) )

    val notinBuild = bd.mk_operByName( TlaSetOper.notin.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.notin.name, n_a ) )
    assert( notinBuild == OperEx( TlaSetOper.notin, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( 
      bd.mk_operByName( TlaSetOper.notin.name, n_a, n_b, n_c ) 
    )

    val capBuild = bd.mk_operByName( TlaSetOper.cap.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.cap.name, n_a ) )
    assert( capBuild == OperEx( TlaSetOper.cap, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.cap.name, n_a, n_b, n_c ) )

    val cupBuild = bd.mk_operByName( TlaSetOper.cup.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.cup.name, n_a ) )
    assert( cupBuild == OperEx( TlaSetOper.cup, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.cup.name, n_a, n_b, n_c ) )

    val unionBuild = bd.mk_operByName( TlaSetOper.union.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.union.name ) )
    assert( unionBuild == OperEx( TlaSetOper.union, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.union.name, n_a, n_b ) )

    val filterBuild = bd.mk_operByName( TlaSetOper.filter.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.filter.name, n_a, n_b ) )
    assert( filterBuild == OperEx( TlaSetOper.filter, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.filter.name, n_a, n_b, n_c, n_d )
    )

    val mapBuild1 = bd.mk_operByNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c )
    val mapBuild2 = bd.mk_operByNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c, n_d, n_e )

    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.map.name, n_a, n_b )
    )
    assert( mapBuild1 == OperEx( TlaSetOper.map, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( 
      bd.mk_operByName( TlaSetOper.map.name, n_a, n_b, n_c, n_d )
    )
    assert( mapBuild2 == OperEx( TlaSetOper.map, n_a, n_b, n_c, n_d, n_e ) )

    val funSetBuild = bd.mk_operByName( TlaSetOper.funSet.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.funSet.name, n_a ) )
    assert( funSetBuild == OperEx( TlaSetOper.funSet, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName(
      TlaSetOper.funSet.name, n_a, n_b, n_c )
    )

    val recSetBuild1 = bd.mk_operByNameOrNull( TlaSetOper.recSet.name )
    val recSetBuild2 = bd.mk_operByNameOrNull( TlaSetOper.recSet.name, n_a, n_b )

    assert( recSetBuild1 == OperEx( TlaSetOper.recSet ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.recSet.name, n_a )
    )
    assert( recSetBuild2 == OperEx( TlaSetOper.recSet, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.recSet.name, n_a, n_b, n_c )
    )

    val seqSetBuild = bd.mk_operByName( TlaSetOper.seqSet.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.seqSet.name ) )
    assert( seqSetBuild == OperEx( TlaSetOper.seqSet, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.seqSet.name, n_a, n_b ) )

    val subsetBuild = bd.mk_operByName( TlaSetOper.subsetProper.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.subsetProper.name, n_a ) )
    assert( subsetBuild == OperEx( TlaSetOper.subsetProper, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.subsetProper.name, n_a, n_b, n_c )
    )

    val subseteqBuild = bd.mk_operByName( TlaSetOper.subseteq.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.subseteq.name, n_a ) )
    assert( subseteqBuild == OperEx( TlaSetOper.subseteq, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.subseteq.name, n_a, n_b, n_c )
    )

    val supsetBuild = bd.mk_operByName( TlaSetOper.supsetProper.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.supsetProper.name, n_a ) )
    assert( supsetBuild == OperEx( TlaSetOper.supsetProper, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.supsetProper.name, n_a, n_b, n_c )
    )

    val supseteqBuild = bd.mk_operByName( TlaSetOper.supseteq.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.supseteq.name, n_a ) )
    assert( supseteqBuild == OperEx( TlaSetOper.supseteq, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.supseteq.name, n_a, n_b, n_c )
    )

    val setminusBuild = bd.mk_operByName( TlaSetOper.setminus.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.setminus.name, n_a ) )
    assert( setminusBuild == OperEx( TlaSetOper.setminus, n_a, n_b ) )
    assertThrows[IllegalArgumentException](
      bd.mk_operByName( TlaSetOper.setminus.name, n_a, n_b, n_c )
    )

    val timesBuild1 = bd.mk_operByName( TlaSetOper.times.name )
    val timesBuild2 = bd.mk_operByName( TlaSetOper.times.name, n_a, n_b )

    assert( timesBuild1 == OperEx( TlaSetOper.times ) )
    assert( timesBuild2 == OperEx( TlaSetOper.times, n_a, n_b ) )

    val powSetBuild = bd.mk_operByName( TlaSetOper.powerset.name, n_a )

    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.powerset.name ) )
    assert( powSetBuild == OperEx( TlaSetOper.powerset, n_a ) )
    assertThrows[IllegalArgumentException]( bd.mk_operByName( TlaSetOper.powerset.name, n_a, n_b ) )
  
  }

  test("Test mk_operByNameOrNull: TlaSetOper"){
    val enumSetBuild1 = bd.mk_operByNameOrNull( TlaSetOper.enumSet.name )
    val enumSetBuild2 = bd.mk_operByNameOrNull( TlaSetOper.enumSet.name, n_a, n_b )

    assert( enumSetBuild1 == OperEx( TlaSetOper.enumSet ) )
    assert( enumSetBuild2 == OperEx( TlaSetOper.enumSet, n_a, n_b ) )

    val inBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.in.name, n_a )
    val inBuild     = bd.mk_operByNameOrNull( TlaSetOper.in.name, n_a, n_b )
    val inBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.in.name, n_a, n_b, n_c )

    assert( inBuildBad1 == NullEx )
    assert( inBuild     == OperEx( TlaSetOper.in, n_a, n_b ) )
    assert( inBuildBad2 == NullEx )

    val notinBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.notin.name, n_a )
    val notinBuild     = bd.mk_operByNameOrNull( TlaSetOper.notin.name, n_a, n_b )
    val notinBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.notin.name, n_a, n_b, n_c )

    assert( notinBuildBad1 == NullEx )
    assert( notinBuild     == OperEx( TlaSetOper.notin, n_a, n_b ) )
    assert( notinBuildBad2 == NullEx )

    val capBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.cap.name, n_a )
    val capBuild     = bd.mk_operByNameOrNull( TlaSetOper.cap.name, n_a, n_b )
    val capBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.cap.name, n_a, n_b, n_c )

    assert( capBuildBad1 == NullEx )
    assert( capBuild     == OperEx( TlaSetOper.cap, n_a, n_b ) )
    assert( capBuildBad2 == NullEx )

    val cupBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.cup.name, n_a )
    val cupBuild     = bd.mk_operByNameOrNull( TlaSetOper.cup.name, n_a, n_b )
    val cupBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.cup.name, n_a, n_b, n_c )

    assert( cupBuildBad1 == NullEx )
    assert( cupBuild     == OperEx( TlaSetOper.cup, n_a, n_b ) )
    assert( cupBuildBad2 == NullEx )

    val unionBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.union.name )
    val unionBuild     = bd.mk_operByNameOrNull( TlaSetOper.union.name, n_a )
    val unionBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.union.name, n_a, n_b )

    assert( unionBuildBad1 == NullEx )
    assert( unionBuild     == OperEx( TlaSetOper.union, n_a ) )
    assert( unionBuildBad2 == NullEx )

    val filterBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.filter.name, n_a, n_b )
    val filterBuild     = bd.mk_operByNameOrNull( TlaSetOper.filter.name, n_a, n_b, n_c )
    val filterBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.filter.name, n_a, n_b, n_c, n_d )

    assert( filterBuildBad1 == NullEx )
    assert( filterBuild     == OperEx( TlaSetOper.filter, n_a, n_b, n_c ) )
    assert( filterBuildBad2 == NullEx )

    val mapBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.map.name, n_a, n_b )
    val mapBuild1    = bd.mk_operByNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c )
    val mapBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c, n_d )
    val mapBuild2 = bd.mk_operByNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c, n_d, n_e )
    
    assert( mapBuildBad1 == NullEx )
    assert( mapBuild1    == OperEx( TlaSetOper.map, n_a, n_b, n_c ) )
    assert( mapBuildBad2 == NullEx )
    assert( mapBuild2    == OperEx( TlaSetOper.map, n_a, n_b, n_c, n_d, n_e ) )

    val funSetBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.funSet.name, n_a )
    val funSetBuild     = bd.mk_operByNameOrNull( TlaSetOper.funSet.name, n_a, n_b )
    val funSetBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.funSet.name, n_a, n_b, n_c )

    assert( funSetBuildBad1 == NullEx )
    assert( funSetBuild     == OperEx( TlaSetOper.funSet, n_a, n_b ) )
    assert( funSetBuildBad2 == NullEx )

    val recSetBuild1    = bd.mk_operByNameOrNull( TlaSetOper.recSet.name )
    val recSetBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.recSet.name, n_a )
    val recSetBuild2    = bd.mk_operByNameOrNull( TlaSetOper.recSet.name, n_a, n_b )
    val recSetBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.recSet.name, n_a, n_b, n_c )

    assert( recSetBuild1    == OperEx( TlaSetOper.recSet ) )
    assert( recSetBuildBad1 == NullEx )
    assert( recSetBuild2    == OperEx( TlaSetOper.recSet, n_a, n_b ) )
    assert( recSetBuildBad2 == NullEx )

    val seqSetBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.seqSet.name )
    val seqSetBuild     = bd.mk_operByNameOrNull( TlaSetOper.seqSet.name, n_a )
    val seqSetBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.seqSet.name, n_a, n_b )

    assert( seqSetBuildBad1 == NullEx )
    assert( seqSetBuild     == OperEx( TlaSetOper.seqSet, n_a ) )
    assert( seqSetBuildBad2 == NullEx )

    val subsetBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.subsetProper.name, n_a )
    val subsetBuild     = bd.mk_operByNameOrNull( TlaSetOper.subsetProper.name, n_a, n_b )
    val subsetBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.subsetProper.name, n_a, n_b, n_c )

    assert( subsetBuildBad1 == NullEx )
    assert( subsetBuild     == OperEx( TlaSetOper.subsetProper, n_a, n_b ) )
    assert( subsetBuildBad2 == NullEx )

    val subseteqBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.subseteq.name, n_a )
    val subseteqBuild     = bd.mk_operByNameOrNull( TlaSetOper.subseteq.name, n_a, n_b )
    val subseteqBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.subseteq.name, n_a, n_b, n_c )

    assert( subseteqBuildBad1 == NullEx )
    assert( subseteqBuild     == OperEx( TlaSetOper.subseteq, n_a, n_b ) )
    assert( subseteqBuildBad2 == NullEx )

    val supsetBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.supsetProper.name, n_a )
    val supsetBuild     = bd.mk_operByNameOrNull( TlaSetOper.supsetProper.name, n_a, n_b )
    val supsetBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.supsetProper.name, n_a, n_b, n_c )

    assert( supsetBuildBad1 == NullEx )
    assert( supsetBuild     == OperEx( TlaSetOper.supsetProper, n_a, n_b ) )
    assert( supsetBuildBad2 == NullEx )

    val supseteqBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.supseteq.name, n_a )
    val supseteqBuild     = bd.mk_operByNameOrNull( TlaSetOper.supseteq.name, n_a, n_b )
    val supseteqBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.supseteq.name, n_a, n_b, n_c )

    assert( supseteqBuildBad1 == NullEx )
    assert( supseteqBuild     == OperEx( TlaSetOper.supseteq, n_a, n_b ) )
    assert( supseteqBuildBad2 == NullEx )

    val setminusBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.setminus.name, n_a )
    val setminusBuild     = bd.mk_operByNameOrNull( TlaSetOper.setminus.name, n_a, n_b )
    val setminusBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.setminus.name, n_a, n_b, n_c )

    assert( setminusBuildBad1 == NullEx )
    assert( setminusBuild     == OperEx( TlaSetOper.setminus, n_a, n_b ) )
    assert( setminusBuildBad2 == NullEx )

    val timesBuild1 = bd.mk_operByNameOrNull( TlaSetOper.times.name )
    val timesBuild2 = bd.mk_operByNameOrNull( TlaSetOper.times.name, n_a, n_b )

    assert( timesBuild1 == OperEx( TlaSetOper.times ) )
    assert( timesBuild2 == OperEx( TlaSetOper.times, n_a, n_b ) )

    val powersetBuildBad1 = bd.mk_operByNameOrNull( TlaSetOper.powerset.name )
    val powersetBuild     = bd.mk_operByNameOrNull( TlaSetOper.powerset.name, n_a )
    val powersetBuildBad2 = bd.mk_operByNameOrNull( TlaSetOper.powerset.name, n_a, n_b )

    assert( powersetBuildBad1 == NullEx )
    assert( powersetBuild     == OperEx( TlaSetOper.powerset, n_a ) )
    assert( powersetBuildBad2 == NullEx )
    
  }

}

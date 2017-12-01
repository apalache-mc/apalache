package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestBuilder extends FunSuite with TestingPredefs {

  import at.forsyte.apalache.tla.lir.{Builder => bd}

  test( "Test direct methods: Names and values" ) {
    val nameBuild = bd.name( "a" )

    assert( nameBuild == NameEx( "a" ) )

    val vBigInt : BigInt = BigInt( "1000000015943534656464398536" )
    val vBigDecimal : BigDecimal = 1.111132454253626474876842798573504607
    val vBool : Boolean = false
    val vString : String = "a string val"

    val biBuild = bd.bigInt( vBigInt )
    val bdBuild = bd.decimal( vBigDecimal )
    val boolBuild = bd.bool( vBool )
    val strBuild = bd.str( vString )

    assert( biBuild == ValEx( TlaInt( vBigInt ) ) )
    assert( bdBuild == ValEx( TlaDecimal( vBigDecimal ) ) )
    assert( boolBuild == ValEx( TlaBool( vBool ) ) )
    assert( strBuild == ValEx( TlaStr( vString ) ) )
  }

  test( "Test direct methods: Declarations" ) {
    val opEx1 = bd.declOp( "A", n_c )
    val opEx2 = bd.declOp( "A", n_x, "x" )
    val opEx3 = bd.declOp( "A", bd.appOp( n_B ), ("B", 0) )
    val opEx4 = bd.declOp( "A", bd.appOp( n_B, n_x ), "x", ("B", 1) )

    assert( opEx1 == TlaOperDecl( "A", List(), n_c ) )
    assert( opEx2 == TlaOperDecl( "A", List( SimpleFormalParam( "x" ) ), n_x ) )
    assert( opEx3 ==
      TlaOperDecl(
        "A",
        List( OperFormalParam( "B", FixedArity( 0 ) ) ),
        OperEx( TlaOper.apply, n_B )
      )
    )
    assert( opEx4 ==
      TlaOperDecl(
        "A",
        List( SimpleFormalParam( "x" ), OperFormalParam( "B", FixedArity( 1 ) ) ),
        OperEx( TlaOper.apply, n_B, n_x )
      )
    )

    val oper1 = opEx1.operator
    val oper2 = opEx2.operator
    val oper3 = opEx3.operator
    val oper4 = opEx4.operator

    val appEx1 = bd.appDecl( opEx1 )
    val appEx2 = bd.appDecl( opEx2, n_a )
    val appEx3 = bd.appDecl( opEx3, n_a )
    val appEx4 = bd.appDecl( opEx4, n_a, n_b )

    assert( appEx1 == OperEx( oper1 ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx1, n_a ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx2) )
    assert( appEx2 == OperEx( oper2, n_a ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx2, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx3 ) )
    assert( appEx3 == OperEx( oper3, n_a ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx3, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx4 ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx4, n_a ) )
    assert( appEx4 == OperEx( oper4, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.appDecl( opEx4, n_a, n_b, n_c ) )
  }

  test( "Test byName: bad calls" ) {
    assertThrows[NoSuchElementException]( bd.byName( "not an operator name", NullEx, n_b ) )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.plus.name, NullEx ) )
  }

  test( "Test byNameOrNull: bad calls" ) {
    val nullBadName = bd.byNameOrNull( "not an operator name", NullEx, n_b )

    assert( nullBadName == NullEx )

    val nullBadArity = bd.byNameOrNull( TlaArithOper.plus.name, NullEx )

    assert( nullBadArity == NullEx )
  }

  test( "Test direct methods: TlaOper" ) {
    val eqBuild1 = bd.eql( n_a, n_b )
    val eqBuild2 = bd.eql( n_a, 2 )

    assert( eqBuild1 == OperEx( TlaOper.eq, n_a, n_b ) )
    assert( eqBuild2 == OperEx( TlaOper.eq, n_a, ValEx( TlaInt( 2 ) ) ) )

    val neBuild1 = bd.neql( n_a, n_b )
    val neBuild2 = bd.neql( n_a, 2 )

    assert( neBuild1 == OperEx( TlaOper.ne, n_a, n_b ) )
    assert( neBuild2 == OperEx( TlaOper.ne, n_a, ValEx( TlaInt( 2 ) ) ) )

    val applyBuild1 = bd.appOp( n_a )
    val applyBuild2 = bd.appOp( n_a, n_b )
    val applyBuild3 = bd.appOp( n_a, n_b, n_c )
    val applyBuild4 = bd.appOp( n_a, n_b, n_c, n_d )

    assert( applyBuild1 == OperEx( TlaOper.apply, n_a ) )
    assert( applyBuild2 == OperEx( TlaOper.apply, n_a, n_b ) )
    assert( applyBuild3 == OperEx( TlaOper.apply, n_a, n_b, n_c ) )
    assert( applyBuild4 == OperEx( TlaOper.apply, n_a, n_b, n_c, n_d ) )

    val chooseBuild1 = bd.choose( n_a, n_b )
    val chooseBuild2 = bd.choose( n_a, n_b, n_c )

    assert( chooseBuild1 == OperEx( TlaOper.chooseUnbounded, n_a, n_b ) )
    assert( chooseBuild2 == OperEx( TlaOper.chooseBounded, n_a, n_b, n_c ) )
  }

  test( "Test byName: TlaOper" ) {
    val eqBuild = bd.byName( TlaOper.eq.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.eq.name, n_a ) )
    assert( eqBuild == OperEx( TlaOper.eq, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.eq.name, n_a, n_b, n_c ) )

    val neBuild = bd.byName( TlaOper.ne.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.ne.name, n_a ) )
    assert( neBuild == OperEx( TlaOper.ne, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.ne.name, n_a, n_b, n_c ) )

    val cbBuild = bd.byName( TlaOper.chooseBounded.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.chooseBounded.name, n_a, n_b ) )
    assert( cbBuild == OperEx( TlaOper.chooseBounded, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.chooseBounded.name, n_a, n_b, n_c, n_d ) )

    val cubBuild = bd.byName( TlaOper.chooseUnbounded.name, n_a, n_b )

    assert( cubBuild == OperEx( TlaOper.chooseUnbounded, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.chooseUnbounded.name, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaOper.chooseUnbounded.name, n_a, n_b, n_c, n_d ) )
  }

  test( "Test byNameOrNull: TlaOper" ) {
    val eqBuildBad1 = bd.byNameOrNull( TlaOper.eq.name, n_a )
    val eqBuild = bd.byNameOrNull( TlaOper.eq.name, n_a, n_b )
    val eqBuildBad2 = bd.byNameOrNull( TlaOper.eq.name, n_a, n_b, n_c )

    assert( eqBuildBad1 == NullEx )
    assert( eqBuild == OperEx( TlaOper.eq, n_a, n_b ) )
    assert( eqBuildBad2 == NullEx )

    val neBuildBad1 = bd.byNameOrNull( TlaOper.ne.name, n_a )
    val neBuild = bd.byNameOrNull( TlaOper.ne.name, n_a, n_b )
    val neBuildBad2 = bd.byNameOrNull( TlaOper.ne.name, n_a, n_b, n_c )

    assert( neBuildBad1 == NullEx )
    assert( neBuild == OperEx( TlaOper.ne, n_a, n_b ) )
    assert( neBuildBad2 == NullEx )

    val cbBuildBad1 = bd.byNameOrNull( TlaOper.chooseBounded.name, n_a, n_b )
    val cbBuild = bd.byNameOrNull( TlaOper.chooseBounded.name, n_a, n_b, n_c )
    val cbBuildBad2 = bd.byNameOrNull( TlaOper.chooseBounded.name, n_a, n_b, n_c, n_d )

    assert( cbBuildBad1 == NullEx )
    assert( cbBuild == OperEx( TlaOper.chooseBounded, n_a, n_b, n_c ) )
    assert( cbBuildBad2 == NullEx )

    val cubBuild = bd.byNameOrNull( TlaOper.chooseUnbounded.name, n_a, n_b )
    val cubBuildBad1 = bd.byNameOrNull( TlaOper.chooseUnbounded.name, n_a, n_b, n_c )
    val cubBuildBad2 = bd.byNameOrNull( TlaOper.chooseUnbounded.name, n_a, n_b, n_c, n_d )

    assert( cubBuild == OperEx( TlaOper.chooseUnbounded, n_a, n_b ) )
    assert( cubBuildBad1 == NullEx )
    assert( cubBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaBoolOper " ) {
    val andBuild1 = bd.and( n_a )
    val andBuild2 = bd.and( n_a, n_b )
    val andBuild3 = bd.and( n_a, n_b, n_c )
    val andBuild4 = bd.and( n_a, n_b, n_c, n_d )

    assert( andBuild1 == OperEx( TlaBoolOper.and, n_a ) )
    assert( andBuild2 == OperEx( TlaBoolOper.and, n_a, n_b ) )
    assert( andBuild3 == OperEx( TlaBoolOper.and, n_a, n_b, n_c ) )
    assert( andBuild4 == OperEx( TlaBoolOper.and, n_a, n_b, n_c, n_d ) )

    val orBuild1 = bd.or( n_a )
    val orBuild2 = bd.or( n_a, n_b )
    val orBuild3 = bd.or( n_a, n_b, n_c )
    val orBuild4 = bd.or( n_a, n_b, n_c, n_d )

    assert( orBuild1 == OperEx( TlaBoolOper.or, n_a ) )
    assert( orBuild2 == OperEx( TlaBoolOper.or, n_a, n_b ) )
    assert( orBuild3 == OperEx( TlaBoolOper.or, n_a, n_b, n_c ) )
    assert( orBuild4 == OperEx( TlaBoolOper.or, n_a, n_b, n_c, n_d ) )

    val notBuild1 = bd.not( n_a )

    assert( notBuild1 == OperEx( TlaBoolOper.not, n_a ) )

    val impliesBuild1 = bd.impl( n_a, n_b )

    assert( impliesBuild1 == OperEx( TlaBoolOper.implies, n_a, n_b ) )

    val equivBuild1 = bd.equiv( n_a, n_b )

    assert( equivBuild1 == OperEx( TlaBoolOper.equiv, n_a, n_b ) )

    val forallBuild1 = bd.forall( n_a, n_b )
    val forallBuild2 = bd.forall( n_a, n_b, n_c )

    assert( forallBuild1 == OperEx( TlaBoolOper.forallUnbounded, n_a, n_b ) )
    assert( forallBuild2 == OperEx( TlaBoolOper.forall, n_a, n_b, n_c ) )

    val existsBuild1 = bd.exists( n_a, n_b )
    val existsBuild2 = bd.exists( n_a, n_b, n_c )

    assert( existsBuild1 == OperEx( TlaBoolOper.existsUnbounded, n_a, n_b ) )
    assert( existsBuild2 == OperEx( TlaBoolOper.exists, n_a, n_b, n_c ) )
  }

  test( "Test byName: TlaBoolOper " ) {
    val andBuild1 = bd.byName( TlaBoolOper.and.name )
    val andBuild2 = bd.byName( TlaBoolOper.and.name, n_a )
    val andBuild3 = bd.byName( TlaBoolOper.and.name, n_a, n_b )

    assert( andBuild1 == OperEx( TlaBoolOper.and ) )
    assert( andBuild2 == OperEx( TlaBoolOper.and, n_a ) )
    assert( andBuild3 == OperEx( TlaBoolOper.and, n_a, n_b ) )

    val orBuild1 = bd.byName( TlaBoolOper.or.name )
    val orBuild2 = bd.byName( TlaBoolOper.or.name, n_a )
    val orBuild3 = bd.byName( TlaBoolOper.or.name, n_a, n_b )

    assert( orBuild1 == OperEx( TlaBoolOper.or ) )
    assert( orBuild2 == OperEx( TlaBoolOper.or, n_a ) )
    assert( orBuild3 == OperEx( TlaBoolOper.or, n_a, n_b ) )

    val notBuild = bd.byName( TlaBoolOper.not.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaBoolOper.not.name ) )
    assert( notBuild == OperEx( TlaBoolOper.not, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaBoolOper.not.name, n_a, n_b ) )

    val impliesBuild = bd.byName( TlaBoolOper.implies.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaBoolOper.implies.name, n_a ) )
    assert( impliesBuild == OperEx( TlaBoolOper.implies, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaBoolOper.implies.name, n_a, n_b, n_c ) )

  }

  test( "Test byNameOrNull: TlaBoolOper " ) {
    val andBuild1 = bd.byNameOrNull( TlaBoolOper.and.name )
    val andBuild2 = bd.byNameOrNull( TlaBoolOper.and.name, n_a )
    val andBuild3 = bd.byNameOrNull( TlaBoolOper.and.name, n_a, n_b )

    assert( andBuild1 == OperEx( TlaBoolOper.and ) )
    assert( andBuild2 == OperEx( TlaBoolOper.and, n_a ) )
    assert( andBuild3 == OperEx( TlaBoolOper.and, n_a, n_b ) )

    val orBuild1 = bd.byNameOrNull( TlaBoolOper.or.name )
    val orBuild2 = bd.byNameOrNull( TlaBoolOper.or.name, n_a )
    val orBuild3 = bd.byNameOrNull( TlaBoolOper.or.name, n_a, n_b )

    assert( orBuild1 == OperEx( TlaBoolOper.or ) )
    assert( orBuild2 == OperEx( TlaBoolOper.or, n_a ) )
    assert( orBuild3 == OperEx( TlaBoolOper.or, n_a, n_b ) )

    val notBuildBad1 = bd.byNameOrNull( TlaBoolOper.not.name )
    val notBuild = bd.byNameOrNull( TlaBoolOper.not.name, n_a )
    val notBuildBad2 = bd.byNameOrNull( TlaBoolOper.not.name, n_a, n_b )

    assert( notBuildBad1 == NullEx )
    assert( notBuild == OperEx( TlaBoolOper.not, n_a ) )
    assert( notBuildBad2 == NullEx )

    val impliesBuildBad1 = bd.byNameOrNull( TlaBoolOper.implies.name, n_a )
    val impliesBuild = bd.byNameOrNull( TlaBoolOper.implies.name, n_a, n_b )
    val impliesBuildBad2 = bd.byNameOrNull( TlaBoolOper.implies.name, n_a, n_b, n_c )

    assert( impliesBuildBad1 == NullEx )
    assert( impliesBuild == OperEx( TlaBoolOper.implies, n_a, n_b ) )
    assert( impliesBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaActionOper" ) {
    val primeBuild1 = bd.prime( n_a )
    val primeBuild2 = bd.prime( "name" )

    assert( primeBuild1 == OperEx( TlaActionOper.prime, n_a ) )
    assert( primeBuild2 == OperEx( TlaActionOper.prime, NameEx( "name" ) ) )

    val primeEqBuild1 = bd.primeEq( "name", n_a )
    val primeEqBuild2 = bd.primeEq( n_a, n_b )
    val primeEqBuild3 = bd.primeEq( "name", 1 )
    val primeEqBuild4 = bd.primeEq( n_a, 2 )
    val primeEqBuild5 = bd.primeEq( "name1", "name2" )

    assert( primeEqBuild1 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( "name" ) ), n_a ) )
    assert( primeEqBuild2 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, n_a ), n_b ) )
    assert( primeEqBuild3 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( "name" ) ), ValEx( TlaInt( 1 ) ) ) )
    assert( primeEqBuild4 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, n_a ), ValEx( TlaInt( 2 ) ) ) )
    assert( primeEqBuild5 == OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( "name1" ) ), NameEx( "name2" ) ) )

    val stutterBuild = bd.stutt( n_a, n_b )

    assert( stutterBuild == OperEx( TlaActionOper.stutter, n_a, n_b ) )

    val nostutterBuild = bd.nostutt( n_a, n_b )

    assert( nostutterBuild == OperEx( TlaActionOper.nostutter, n_a, n_b ) )

    val enabledBuild = bd.enabled( n_a )

    assert( enabledBuild == OperEx( TlaActionOper.enabled, n_a ) )

    val unchangedBuild = bd.unchanged( n_a )

    assert( unchangedBuild == OperEx( TlaActionOper.unchanged, n_a ) )

    val compositionBuild = bd.comp( n_a, n_b )

    assert( compositionBuild == OperEx( TlaActionOper.composition, n_a, n_b ) )

  }

  test( "Test byName: TlaActionOper" ) {
    val primeBuild = bd.byNameOrNull( TlaActionOper.prime.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.prime.name ) )
    assert( primeBuild == OperEx( TlaActionOper.prime, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.prime.name, n_a, n_b ) )

    val stutterBuild = bd.byName( TlaActionOper.stutter.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.stutter.name, n_a ) )
    assert( stutterBuild == OperEx( TlaActionOper.stutter, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.stutter.name, n_a, n_b, n_c ) )

    val nostutterBuild = bd.byName( TlaActionOper.nostutter.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.nostutter.name, n_a ) )
    assert( nostutterBuild == OperEx( TlaActionOper.nostutter, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.nostutter.name, n_a, n_b, n_c ) )

    val enabledBuild = bd.byName( TlaActionOper.enabled.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.enabled.name ) )
    assert( enabledBuild == OperEx( TlaActionOper.enabled, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.enabled.name, n_a, n_b ) )

    val unchangedBuild = bd.byName( TlaActionOper.unchanged.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.unchanged.name ) )
    assert( unchangedBuild == OperEx( TlaActionOper.unchanged, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.unchanged.name, n_a, n_b ) )

    val compositionBuild = bd.byName( TlaActionOper.composition.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.composition.name, n_a ) )
    assert( compositionBuild == OperEx( TlaActionOper.composition, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaActionOper.composition.name, n_a, n_b, n_c ) )
  }

  test( "Test byNameOrNull: TlaActionOper" ) {
    val primeBuildBad1 = bd.byNameOrNull( TlaActionOper.prime.name )
    val primeBuild = bd.byNameOrNull( TlaActionOper.prime.name, n_a )
    val primeBuildBad2 = bd.byNameOrNull( TlaActionOper.prime.name, n_a, n_b )

    assert( primeBuildBad1 == NullEx )
    assert( primeBuild == OperEx( TlaActionOper.prime, n_a ) )
    assert( primeBuildBad2 == NullEx )

    val stutterBuildBad1 = bd.byNameOrNull( TlaActionOper.stutter.name, n_a )
    val stutterBuild = bd.byNameOrNull( TlaActionOper.stutter.name, n_a, n_b )
    val stutterBuildBad2 = bd.byNameOrNull( TlaActionOper.stutter.name, n_a, n_b, n_c )

    assert( stutterBuildBad1 == NullEx )
    assert( stutterBuild == OperEx( TlaActionOper.stutter, n_a, n_b ) )
    assert( stutterBuildBad2 == NullEx )

    val nostutterBuildBad1 = bd.byNameOrNull( TlaActionOper.nostutter.name, n_a )
    val nostutterBuild = bd.byNameOrNull( TlaActionOper.nostutter.name, n_a, n_b )
    val nostutterBuildBad2 = bd.byNameOrNull( TlaActionOper.nostutter.name, n_a, n_b, n_c )

    assert( nostutterBuildBad1 == NullEx )
    assert( nostutterBuild == OperEx( TlaActionOper.nostutter, n_a, n_b ) )
    assert( nostutterBuildBad2 == NullEx )

    val enabledBuildBad1 = bd.byNameOrNull( TlaActionOper.enabled.name )
    val enabledBuild = bd.byNameOrNull( TlaActionOper.enabled.name, n_a )
    val enabledBuildBad2 = bd.byNameOrNull( TlaActionOper.enabled.name, n_a, n_b )

    assert( enabledBuildBad1 == NullEx )
    assert( enabledBuild == OperEx( TlaActionOper.enabled, n_a ) )
    assert( enabledBuildBad2 == NullEx )

    val unchangedBuildBad1 = bd.byNameOrNull( TlaActionOper.unchanged.name )
    val unchangedBuild = bd.byNameOrNull( TlaActionOper.unchanged.name, n_a )
    val unchangedBuildBad2 = bd.byNameOrNull( TlaActionOper.unchanged.name, n_a, n_b )

    assert( unchangedBuildBad1 == NullEx )
    assert( unchangedBuild == OperEx( TlaActionOper.unchanged, n_a ) )
    assert( unchangedBuildBad2 == NullEx )

    val compositionBuildBad1 = bd.byNameOrNull( TlaActionOper.composition.name, n_a )
    val compositionBuild = bd.byNameOrNull( TlaActionOper.composition.name, n_a, n_b )
    val compositionBuildBad2 = bd.byNameOrNull( TlaActionOper.composition.name, n_a, n_b, n_c )

    assert( compositionBuildBad1 == NullEx )
    assert( compositionBuild == OperEx( TlaActionOper.composition, n_a, n_b ) )
    assert( compositionBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaControlOper" ) {

    val caseBuild1 = bd.caseAny( n_a, n_b )
    val caseBuild2 = bd.caseAny( n_a, n_b, n_c )
    val caseBuild3 = bd.caseAny( n_a, n_b, n_c, n_d )
    val caseBuild4 = bd.caseAny( n_a, n_b, n_c, n_d, n_e )
    val caseBuild5 = bd.caseAny( n_a, n_b, n_c, n_d, n_e, n_f )
    val caseBuild6 = bd.caseAny( n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assert( caseBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assert( caseBuild4 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assert( caseBuild5 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert( caseBuild6 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g ) )

    val caseSplitBuild1 = bd.caseSplit( n_a, n_b )
    val caseSplitBuild2 = bd.caseSplit( n_a, n_b, n_c, n_d )
    val caseSplitBuild3 = bd.caseSplit( n_a, n_b, n_c, n_d, n_e, n_f )

    assert( caseSplitBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.caseSplit( n_a, n_b, n_c ) )
    assert( caseSplitBuild2 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assertThrows[IllegalArgumentException]( bd.caseSplit( n_a, n_b, n_c, n_d, n_e ) )
    assert( caseSplitBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )

    val caseOtherBuild1 = bd.caseOther( n_a, n_b, n_c )
    val caseOtherBuild2 = bd.caseOther( n_a, n_b, n_c, n_d, n_e )
    val caseOtherBuild3 = bd.caseOther( n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseOtherBuild1 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.caseOther( n_a, n_b, n_c, n_d ) )
    assert( caseOtherBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.caseOther( n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert( caseOtherBuild3 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g ) )

    val iteBuild1 = bd.ite( n_a, n_b, n_c )

    assert( iteBuild1 == OperEx( TlaControlOper.ifThenElse, n_a, n_b, n_c ) )

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

  test( "Test byName: TlaControlOper" ) {
    val caseBuild1 = bd.byName( TlaControlOper.caseNoOther.name, n_a, n_b )
    val caseBuild2 = bd.byName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )
    val caseBuild3 = bd.byName( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d )
    val caseBuild4 = bd.byName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e )
    val caseBuild5 = bd.byName( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d, n_e, n_f )
    val caseBuild6 = bd.byName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assert( caseBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assert( caseBuild4 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assert( caseBuild5 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert( caseBuild6 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g ) )

    val caseNoOtherBuild = bd.byName( TlaControlOper.caseNoOther.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.caseNoOther.name ) )
    assert( caseNoOtherBuild == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.caseNoOther.name, n_a, n_b, n_c ) )

    val caseWithOtherBuild = bd.byName( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.caseWithOther.name ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.caseWithOther.name, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.caseWithOther.name, n_a, n_b ) )
    assert( caseWithOtherBuild == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )

    val iteBuild = bd.byName( TlaControlOper.ifThenElse.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.ifThenElse.name, n_a, n_b ) )
    assert( iteBuild == OperEx( TlaControlOper.ifThenElse, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaControlOper.ifThenElse.name, n_a, n_b, n_c, n_d ) )
  }

  test( "Test byNameOrNull: TlaControlOper" ) {
    val caseBuild1 = bd.byNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b )
    val caseBuild2 = bd.byNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )
    val caseBuild3 = bd.byNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d )
    val caseBuild4 = bd.byNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e )
    val caseBuild5 = bd.byNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b, n_c, n_d, n_e, n_f )
    val caseBuild6 = bd.byNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c, n_d, n_e, n_f, n_g )

    assert( caseBuild1 == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseBuild2 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )
    assert( caseBuild3 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d ) )
    assert( caseBuild4 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e ) )
    assert( caseBuild5 == OperEx( TlaControlOper.caseNoOther, n_a, n_b, n_c, n_d, n_e, n_f ) )
    assert( caseBuild6 == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c, n_d, n_e, n_f, n_g ) )

    val caseNoOtherBuildEmpty = bd.byNameOrNull( TlaControlOper.caseNoOther.name )
    val caseNoOtherBuild = bd.byNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b )
    val caseNoOtherBuildBad = bd.byNameOrNull( TlaControlOper.caseNoOther.name, n_a, n_b, n_c )

    assert( caseNoOtherBuildEmpty == NullEx )
    assert( caseNoOtherBuild == OperEx( TlaControlOper.caseNoOther, n_a, n_b ) )
    assert( caseNoOtherBuildBad == NullEx )

    val caseWithOtherBuildEmpty = bd.byNameOrNull( TlaControlOper.caseWithOther.name )
    val caseWithOtherBuildSingle = bd.byNameOrNull( TlaControlOper.caseWithOther.name, n_a )
    val caseWithOtherBuildBad = bd.byNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b )
    val caseWithOtherBuild = bd.byNameOrNull( TlaControlOper.caseWithOther.name, n_a, n_b, n_c )

    assert( caseWithOtherBuildEmpty == NullEx )
    assert( caseWithOtherBuildSingle == NullEx )
    assert( caseWithOtherBuildBad == NullEx )
    assert( caseWithOtherBuild == OperEx( TlaControlOper.caseWithOther, n_a, n_b, n_c ) )

    val iteBuildBad1 = bd.byNameOrNull( TlaControlOper.ifThenElse.name, n_a, n_b )
    val iteBuild = bd.byNameOrNull( TlaControlOper.ifThenElse.name, n_a, n_b, n_c )
    val iteBuildBad2 = bd.byNameOrNull( TlaControlOper.ifThenElse.name, n_a, n_b, n_c, n_d )

    assert( iteBuildBad1 == NullEx )
    assert( iteBuild == OperEx( TlaControlOper.ifThenElse, n_a, n_b, n_c ) )
    assert( iteBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaTempOper" ) {
    val AABuild = bd.AA( n_a, n_b )

    assert( AABuild == OperEx( TlaTempOper.AA, n_a, n_b ) )

    val EEBuild = bd.EE( n_a, n_b )

    assert( EEBuild == OperEx( TlaTempOper.EE, n_a, n_b ) )

    val boxBuild = bd.box( n_a )

    assert( boxBuild == OperEx( TlaTempOper.box, n_a ) )

    val diamondBuild = bd.diamond( n_a )

    assert( diamondBuild == OperEx( TlaTempOper.diamond, n_a ) )

    val leadsToBuild = bd.leadsTo( n_a, n_b )

    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, n_a, n_b ) )

    val guaranteesBuild = bd.guarantees( n_a, n_b )

    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, n_a, n_b ) )

    val strongFairnessBuild = bd.SF( n_a, n_b )

    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, n_a, n_b ) )

    val weakFairnessBuild = bd.WF( n_a, n_b )

    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, n_a, n_b ) )
  }

  test( "Test byName: TlaTempOper" ) {
    val AABuild = bd.byName( TlaTempOper.AA.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.AA.name, n_a ) )
    assert( AABuild == OperEx( TlaTempOper.AA, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.AA.name, n_a, n_b, n_c ) )

    val EEBuild = bd.byName( TlaTempOper.EE.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.EE.name, n_a ) )
    assert( EEBuild == OperEx( TlaTempOper.EE, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.EE.name, n_a, n_b, n_c ) )

    val boxBuild = bd.byName( TlaTempOper.box.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.box.name ) )
    assert( boxBuild == OperEx( TlaTempOper.box, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.box.name, n_a, n_b ) )

    val diamondBuild = bd.byName( TlaTempOper.diamond.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.diamond.name ) )
    assert( diamondBuild == OperEx( TlaTempOper.diamond, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.diamond.name, n_a, n_b ) )

    val leadsToBuild = bd.byName( TlaTempOper.leadsTo.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.leadsTo.name, n_a ) )
    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.leadsTo.name, n_a, n_b, n_c ) )

    val guaranteesBuild = bd.byName( TlaTempOper.guarantees.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.guarantees.name, n_a ) )
    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.guarantees.name, n_a, n_b, n_c ) )

    val strongFairnessBuild = bd.byName( TlaTempOper.strongFairness.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.strongFairness.name, n_a ) )
    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.strongFairness.name, n_a, n_b, n_c ) )

    val weakFairnessBuild = bd.byName( TlaTempOper.weakFairness.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.weakFairness.name, n_a ) )
    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaTempOper.weakFairness.name, n_a, n_b, n_c ) )

  }

  test( "Test byNameOrNull: TlaTempOper" ) {
    val AABuildBad1 = bd.byNameOrNull( TlaTempOper.AA.name, n_a )
    val AABuild = bd.byNameOrNull( TlaTempOper.AA.name, n_a, n_b )
    val AABuildBad2 = bd.byNameOrNull( TlaTempOper.AA.name, n_a, n_b, n_c )

    assert( AABuildBad1 == NullEx )
    assert( AABuild == OperEx( TlaTempOper.AA, n_a, n_b ) )
    assert( AABuildBad2 == NullEx )

    val EEBuildBad1 = bd.byNameOrNull( TlaTempOper.EE.name, n_a )
    val EEBuild = bd.byNameOrNull( TlaTempOper.EE.name, n_a, n_b )
    val EEBuildBad2 = bd.byNameOrNull( TlaTempOper.EE.name, n_a, n_b, n_c )

    assert( EEBuildBad1 == NullEx )
    assert( EEBuild == OperEx( TlaTempOper.EE, n_a, n_b ) )
    assert( EEBuildBad2 == NullEx )

    val boxBuildBad1 = bd.byNameOrNull( TlaTempOper.box.name )
    val boxBuild = bd.byNameOrNull( TlaTempOper.box.name, n_a )
    val boxBuildBad2 = bd.byNameOrNull( TlaTempOper.box.name, n_a, n_b )

    assert( boxBuildBad1 == NullEx )
    assert( boxBuild == OperEx( TlaTempOper.box, n_a ) )
    assert( boxBuildBad2 == NullEx )

    val diamondBuildBad1 = bd.byNameOrNull( TlaTempOper.diamond.name )
    val diamondBuild = bd.byNameOrNull( TlaTempOper.diamond.name, n_a )
    val diamondBuildBad2 = bd.byNameOrNull( TlaTempOper.diamond.name, n_a, n_b )

    assert( diamondBuildBad1 == NullEx )
    assert( diamondBuild == OperEx( TlaTempOper.diamond, n_a ) )
    assert( diamondBuildBad2 == NullEx )

    val leadsToBuildBad1 = bd.byNameOrNull( TlaTempOper.leadsTo.name, n_a )
    val leadsToBuild = bd.byNameOrNull( TlaTempOper.leadsTo.name, n_a, n_b )
    val leadsToBuildBad2 = bd.byNameOrNull( TlaTempOper.leadsTo.name, n_a, n_b, n_c )

    assert( leadsToBuildBad1 == NullEx )
    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, n_a, n_b ) )
    assert( leadsToBuildBad2 == NullEx )

    val guaranteesBuildBad1 = bd.byNameOrNull( TlaTempOper.guarantees.name, n_a )
    val guaranteesBuild = bd.byNameOrNull( TlaTempOper.guarantees.name, n_a, n_b )
    val guaranteesBuildBad2 = bd.byNameOrNull( TlaTempOper.guarantees.name, n_a, n_b, n_c )

    assert( guaranteesBuildBad1 == NullEx )
    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, n_a, n_b ) )
    assert( guaranteesBuildBad2 == NullEx )

    val strongFairnessBuildBad1 = bd.byNameOrNull( TlaTempOper.strongFairness.name, n_a )
    val strongFairnessBuild = bd.byNameOrNull( TlaTempOper.strongFairness.name, n_a, n_b )
    val strongFairnessBuildBad2 = bd.byNameOrNull( TlaTempOper.strongFairness.name, n_a, n_b, n_c )

    assert( strongFairnessBuildBad1 == NullEx )
    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, n_a, n_b ) )
    assert( strongFairnessBuildBad2 == NullEx )

    val weakFairnessBuildBad1 = bd.byNameOrNull( TlaTempOper.weakFairness.name, n_a )
    val weakFairnessBuild = bd.byNameOrNull( TlaTempOper.weakFairness.name, n_a, n_b )
    val weakFairnessBuildBad2 = bd.byNameOrNull( TlaTempOper.weakFairness.name, n_a, n_b, n_c )

    assert( weakFairnessBuildBad1 == NullEx )
    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, n_a, n_b ) )
    assert( weakFairnessBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaArithOper" ) {
    val sumBuild1 = bd.sum()
    val sumBuild2 = bd.sum( n_a, n_b )

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, n_a, n_b ) )

    val plusBuild1 = bd.plus( n_a, n_b )
    val plusBuild2 = bd.plus( n_a, 2 )
    val plusBuild3 = bd.plus( 1, n_b )
    val plusBuild4 = bd.plus( 1, 2 )

    assert( plusBuild1 == OperEx( TlaArithOper.plus, n_a, n_b ) )
    assert( plusBuild2 == OperEx( TlaArithOper.plus, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( plusBuild3 == OperEx( TlaArithOper.plus, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( plusBuild4 == OperEx( TlaArithOper.plus, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val minusBuild1 = bd.minus( n_a, n_b )
    val minusBuild2 = bd.minus( n_a, 2 )
    val minusBuild3 = bd.minus( 1, n_b )
    val minusBuild4 = bd.minus( 1, 2 )

    assert( minusBuild1 == OperEx( TlaArithOper.minus, n_a, n_b ) )
    assert( minusBuild2 == OperEx( TlaArithOper.minus, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( minusBuild3 == OperEx( TlaArithOper.minus, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( minusBuild4 == OperEx( TlaArithOper.minus, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val uminusBuild = bd.uminus( n_a )

    assert( uminusBuild == OperEx( TlaArithOper.uminus, n_a ) )

    val prodBuild1 = bd.prod()
    val prodBuild2 = bd.prod( n_a, n_b )

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, n_a, n_b ) )

    val multBuild1 = bd.mult( n_a, n_b )
    val multBuild2 = bd.mult( n_a, 2 )
    val multBuild3 = bd.mult( 1, n_b )
    val multBuild4 = bd.mult( 1, 2 )

    assert( multBuild1 == OperEx( TlaArithOper.mult, n_a, n_b ) )
    assert( multBuild2 == OperEx( TlaArithOper.mult, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( multBuild3 == OperEx( TlaArithOper.mult, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( multBuild4 == OperEx( TlaArithOper.mult, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val divBuild1 = bd.div( n_a, n_b )
    val divBuild2 = bd.div( n_a, 2 )
    val divBuild3 = bd.div( 1, n_b )
    val divBuild4 = bd.div( 1, 2 )

    assert( divBuild1 == OperEx( TlaArithOper.div, n_a, n_b ) )
    assert( divBuild2 == OperEx( TlaArithOper.div, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( divBuild3 == OperEx( TlaArithOper.div, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( divBuild4 == OperEx( TlaArithOper.div, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val modBuild1 = bd.mod( n_a, n_b )
    val modBuild2 = bd.mod( n_a, 2 )
    val modBuild3 = bd.mod( 1, n_b )
    val modBuild4 = bd.mod( 1, 2 )

    assert( modBuild1 == OperEx( TlaArithOper.mod, n_a, n_b ) )
    assert( modBuild2 == OperEx( TlaArithOper.mod, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( modBuild3 == OperEx( TlaArithOper.mod, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( modBuild4 == OperEx( TlaArithOper.mod, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val realDivBuild1 = bd.rDiv( n_a, n_b )
    val realDivBuild2 = bd.rDiv( n_a, 2 )
    val realDivBuild3 = bd.rDiv( 1, n_b )
    val realDivBuild4 = bd.rDiv( 1, 2 )

    assert( realDivBuild1 == OperEx( TlaArithOper.realDiv, n_a, n_b ) )
    assert( realDivBuild2 == OperEx( TlaArithOper.realDiv, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( realDivBuild3 == OperEx( TlaArithOper.realDiv, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( realDivBuild4 == OperEx( TlaArithOper.realDiv, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val expBuild1 = bd.exp( n_a, n_b )
    val expBuild2 = bd.exp( n_a, 2 )
    val expBuild3 = bd.exp( 1, n_b )
    val expBuild4 = bd.exp( 1, 2 )

    assert( expBuild1 == OperEx( TlaArithOper.exp, n_a, n_b ) )
    assert( expBuild2 == OperEx( TlaArithOper.exp, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( expBuild3 == OperEx( TlaArithOper.exp, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( expBuild4 == OperEx( TlaArithOper.exp, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val dotdotBuild1 = bd.dotdot( n_a, n_b )
    val dotdotBuild2 = bd.dotdot( n_a, 2 )
    val dotdotBuild3 = bd.dotdot( 1, n_b )
    val dotdotBuild4 = bd.dotdot( 1, 2 )

    assert( dotdotBuild1 == OperEx( TlaArithOper.dotdot, n_a, n_b ) )
    assert( dotdotBuild2 == OperEx( TlaArithOper.dotdot, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( dotdotBuild3 == OperEx( TlaArithOper.dotdot, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( dotdotBuild4 == OperEx( TlaArithOper.dotdot, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val ltBuild1 = bd.lt( n_a, n_b )
    val ltBuild2 = bd.lt( n_a, 2 )
    val ltBuild3 = bd.lt( 1, n_b )
    val ltBuild4 = bd.lt( 1, 2 )

    assert( ltBuild1 == OperEx( TlaArithOper.lt, n_a, n_b ) )
    assert( ltBuild2 == OperEx( TlaArithOper.lt, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( ltBuild3 == OperEx( TlaArithOper.lt, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( ltBuild4 == OperEx( TlaArithOper.lt, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val gtBuild1 = bd.gt( n_a, n_b )
    val gtBuild2 = bd.gt( n_a, 2 )
    val gtBuild3 = bd.gt( 1, n_b )
    val gtBuild4 = bd.gt( 1, 2 )

    assert( gtBuild1 == OperEx( TlaArithOper.gt, n_a, n_b ) )
    assert( gtBuild2 == OperEx( TlaArithOper.gt, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( gtBuild3 == OperEx( TlaArithOper.gt, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( gtBuild4 == OperEx( TlaArithOper.gt, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val leBuild1 = bd.le( n_a, n_b )
    val leBuild2 = bd.le( n_a, 2 )
    val leBuild3 = bd.le( 1, n_b )
    val leBuild4 = bd.le( 1, 2 )

    assert( leBuild1 == OperEx( TlaArithOper.le, n_a, n_b ) )
    assert( leBuild2 == OperEx( TlaArithOper.le, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( leBuild3 == OperEx( TlaArithOper.le, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( leBuild4 == OperEx( TlaArithOper.le, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )

    val geBuild1 = bd.ge( n_a, n_b )
    val geBuild2 = bd.ge( n_a, 2 )
    val geBuild3 = bd.ge( 1, n_b )
    val geBuild4 = bd.ge( 1, 2 )

    assert( geBuild1 == OperEx( TlaArithOper.ge, n_a, n_b ) )
    assert( geBuild2 == OperEx( TlaArithOper.ge, n_a, ValEx( TlaInt( 2 ) ) ) )
    assert( geBuild3 == OperEx( TlaArithOper.ge, ValEx( TlaInt( 1 ) ), n_b ) )
    assert( geBuild4 == OperEx( TlaArithOper.ge, ValEx( TlaInt( 1 ) ), ValEx( TlaInt( 2 ) ) ) )
  }

  test( "Test byName: TlaArithOper" ) {
    val sumBuild1 = bd.byName( TlaArithOper.sum.name )
    val sumBuild2 = bd.byName( TlaArithOper.sum.name, n_a, n_b )

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, n_a, n_b ) )

    val plusBuild = bd.byName( TlaArithOper.plus.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.plus.name, n_a ) )
    assert( plusBuild == OperEx( TlaArithOper.plus, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.plus.name, n_a, n_b, n_c ) )

    val minusBuild = bd.byName( TlaArithOper.minus.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.minus.name, n_a ) )
    assert( minusBuild == OperEx( TlaArithOper.minus, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.minus.name, n_a, n_b, n_c ) )

    val uminusBuild = bd.byName( TlaArithOper.uminus.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.uminus.name ) )
    assert( uminusBuild == OperEx( TlaArithOper.uminus, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.uminus.name, n_a, n_b, n_c ) )

    val prodBuild1 = bd.byName( TlaArithOper.prod.name )
    val prodBuild2 = bd.byName( TlaArithOper.prod.name, n_a, n_b )

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, n_a, n_b ) )

    val multBuild = bd.byName( TlaArithOper.mult.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.mult.name, n_a ) )
    assert( multBuild == OperEx( TlaArithOper.mult, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.mult.name, n_a, n_b, n_c ) )

    val divBuild = bd.byName( TlaArithOper.div.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.div.name, n_a ) )
    assert( divBuild == OperEx( TlaArithOper.div, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.div.name, n_a, n_b, n_c ) )

    val modBuild = bd.byName( TlaArithOper.mod.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.mod.name, n_a ) )
    assert( modBuild == OperEx( TlaArithOper.mod, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.mod.name, n_a, n_b, n_c ) )

    val realDivBuild = bd.byName( TlaArithOper.realDiv.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.realDiv.name, n_a ) )
    assert( realDivBuild == OperEx( TlaArithOper.realDiv, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.realDiv.name, n_a, n_b, n_c ) )

    val expBuild = bd.byName( TlaArithOper.exp.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.exp.name, n_a ) )
    assert( expBuild == OperEx( TlaArithOper.exp, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.exp.name, n_a, n_b, n_c ) )

    val dotdotBuild = bd.byName( TlaArithOper.dotdot.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.dotdot.name, n_a ) )
    assert( dotdotBuild == OperEx( TlaArithOper.dotdot, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.dotdot.name, n_a, n_b, n_c ) )

    val ltBuild = bd.byName( TlaArithOper.lt.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.lt.name, n_a ) )
    assert( ltBuild == OperEx( TlaArithOper.lt, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.lt.name, n_a, n_b, n_c ) )

    val gtBuild = bd.byName( TlaArithOper.gt.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.gt.name, n_a ) )
    assert( gtBuild == OperEx( TlaArithOper.gt, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.gt.name, n_a, n_b, n_c ) )

    val leBuild = bd.byName( TlaArithOper.le.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.le.name, n_a ) )
    assert( leBuild == OperEx( TlaArithOper.le, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.le.name, n_a, n_b, n_c ) )

    val geBuild = bd.byName( TlaArithOper.ge.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.ge.name, n_a ) )
    assert( geBuild == OperEx( TlaArithOper.ge, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaArithOper.ge.name, n_a, n_b, n_c ) )
  }

  test( "Test byNameOrNull: TlaArithOper" ) {
    val sumBuild1 = bd.byNameOrNull( TlaArithOper.sum.name )
    val sumBuild2 = bd.byNameOrNull( TlaArithOper.sum.name, n_a, n_b )

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, n_a, n_b ) )

    val plusBuildBad1 = bd.byNameOrNull( TlaArithOper.plus.name, n_a )
    val plusBuild = bd.byNameOrNull( TlaArithOper.plus.name, n_a, n_b )
    val plusBuildBad2 = bd.byNameOrNull( TlaArithOper.plus.name, n_a, n_b, n_c )

    assert( plusBuildBad1 == NullEx )
    assert( plusBuild == OperEx( TlaArithOper.plus, n_a, n_b ) )
    assert( plusBuildBad2 == NullEx )

    val minusBuildBad1 = bd.byNameOrNull( TlaArithOper.minus.name, n_a )
    val minusBuild = bd.byNameOrNull( TlaArithOper.minus.name, n_a, n_b )
    val minusBuildBad2 = bd.byNameOrNull( TlaArithOper.minus.name, n_a, n_b, n_c )

    assert( minusBuildBad1 == NullEx )
    assert( minusBuild == OperEx( TlaArithOper.minus, n_a, n_b ) )
    assert( minusBuildBad2 == NullEx )

    val uminusBuildBad1 = bd.byNameOrNull( TlaArithOper.uminus.name )
    val uminusBuild = bd.byNameOrNull( TlaArithOper.uminus.name, n_a )
    val uminusBuildBad2 = bd.byNameOrNull( TlaArithOper.uminus.name, n_a, n_b, n_c )

    assert( uminusBuildBad1 == NullEx )
    assert( uminusBuild == OperEx( TlaArithOper.uminus, n_a ) )
    assert( uminusBuildBad2 == NullEx )

    val prodBuild1 = bd.byNameOrNull( TlaArithOper.prod.name )
    val prodBuild2 = bd.byNameOrNull( TlaArithOper.prod.name, n_a, n_b )

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, n_a, n_b ) )

    val multBuildBad1 = bd.byNameOrNull( TlaArithOper.mult.name, n_a )
    val multBuild = bd.byNameOrNull( TlaArithOper.mult.name, n_a, n_b )
    val multBuildBad2 = bd.byNameOrNull( TlaArithOper.mult.name, n_a, n_b, n_c )

    assert( multBuildBad1 == NullEx )
    assert( multBuild == OperEx( TlaArithOper.mult, n_a, n_b ) )
    assert( multBuildBad2 == NullEx )

    val divBuildBad1 = bd.byNameOrNull( TlaArithOper.div.name, n_a )
    val divBuild = bd.byNameOrNull( TlaArithOper.div.name, n_a, n_b )
    val divBuildBad2 = bd.byNameOrNull( TlaArithOper.div.name, n_a, n_b, n_c )

    assert( divBuildBad1 == NullEx )
    assert( divBuild == OperEx( TlaArithOper.div, n_a, n_b ) )
    assert( divBuildBad2 == NullEx )

    val modBuildBad1 = bd.byNameOrNull( TlaArithOper.mod.name, n_a )
    val modBuild = bd.byNameOrNull( TlaArithOper.mod.name, n_a, n_b )
    val modBuildBad2 = bd.byNameOrNull( TlaArithOper.mod.name, n_a, n_b, n_c )

    assert( modBuildBad1 == NullEx )
    assert( modBuild == OperEx( TlaArithOper.mod, n_a, n_b ) )
    assert( modBuildBad2 == NullEx )

    val realDivBuildBad1 = bd.byNameOrNull( TlaArithOper.realDiv.name, n_a )
    val realDivBuild = bd.byNameOrNull( TlaArithOper.realDiv.name, n_a, n_b )
    val realDivBuildBad2 = bd.byNameOrNull( TlaArithOper.realDiv.name, n_a, n_b, n_c )

    assert( realDivBuildBad1 == NullEx )
    assert( realDivBuild == OperEx( TlaArithOper.realDiv, n_a, n_b ) )
    assert( realDivBuildBad2 == NullEx )

    val expBuildBad1 = bd.byNameOrNull( TlaArithOper.exp.name, n_a )
    val expBuild = bd.byNameOrNull( TlaArithOper.exp.name, n_a, n_b )
    val expBuildBad2 = bd.byNameOrNull( TlaArithOper.exp.name, n_a, n_b, n_c )

    assert( expBuildBad1 == NullEx )
    assert( expBuild == OperEx( TlaArithOper.exp, n_a, n_b ) )
    assert( expBuildBad2 == NullEx )

    val dotdotBuildBad1 = bd.byNameOrNull( TlaArithOper.dotdot.name, n_a )
    val dotdotBuild = bd.byNameOrNull( TlaArithOper.dotdot.name, n_a, n_b )
    val dotdotBuildBad2 = bd.byNameOrNull( TlaArithOper.dotdot.name, n_a, n_b, n_c )

    assert( dotdotBuildBad1 == NullEx )
    assert( dotdotBuild == OperEx( TlaArithOper.dotdot, n_a, n_b ) )
    assert( dotdotBuildBad2 == NullEx )

    val ltBuildBad1 = bd.byNameOrNull( TlaArithOper.lt.name, n_a )
    val ltBuild = bd.byNameOrNull( TlaArithOper.lt.name, n_a, n_b )
    val ltBuildBad2 = bd.byNameOrNull( TlaArithOper.lt.name, n_a, n_b, n_c )

    assert( ltBuildBad1 == NullEx )
    assert( ltBuild == OperEx( TlaArithOper.lt, n_a, n_b ) )
    assert( ltBuildBad2 == NullEx )

    val gtBuildBad1 = bd.byNameOrNull( TlaArithOper.gt.name, n_a )
    val gtBuild = bd.byNameOrNull( TlaArithOper.gt.name, n_a, n_b )
    val gtBuildBad2 = bd.byNameOrNull( TlaArithOper.gt.name, n_a, n_b, n_c )

    assert( gtBuildBad1 == NullEx )
    assert( gtBuild == OperEx( TlaArithOper.gt, n_a, n_b ) )
    assert( gtBuildBad2 == NullEx )

    val leBuildBad1 = bd.byNameOrNull( TlaArithOper.le.name, n_a )
    val leBuild = bd.byNameOrNull( TlaArithOper.le.name, n_a, n_b )
    val leBuildBad2 = bd.byNameOrNull( TlaArithOper.le.name, n_a, n_b, n_c )

    assert( leBuildBad1 == NullEx )
    assert( leBuild == OperEx( TlaArithOper.le, n_a, n_b ) )
    assert( leBuildBad2 == NullEx )

    val geBuildBad1 = bd.byNameOrNull( TlaArithOper.ge.name, n_a )
    val geBuild = bd.byNameOrNull( TlaArithOper.ge.name, n_a, n_b )
    val geBuildBad2 = bd.byNameOrNull( TlaArithOper.ge.name, n_a, n_b, n_c )

    assert( geBuildBad1 == NullEx )
    assert( geBuild == OperEx( TlaArithOper.ge, n_a, n_b ) )
    assert( geBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaFiniteSetOper" ) {
    val cardinalityBuild = bd.card( n_a )

    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, n_a ) )

    val isFiniteSetBuild = bd.isFin( n_a )

    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, n_a ) )
  }

  test( "Test byName: TlaFiniteSetOper" ) {
    val cardinalityBuild = bd.byName( TlaFiniteSetOper.cardinality.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFiniteSetOper.cardinality.name ) )
    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFiniteSetOper.cardinality.name, n_a, n_b, n_c ) )

    val isFiniteSetBuild = bd.byName( TlaFiniteSetOper.isFiniteSet.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFiniteSetOper.isFiniteSet.name ) )
    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFiniteSetOper.isFiniteSet.name, n_a, n_b, n_c ) )
  }

  test( "Test byNameOrNull: TlaFiniteSetOper" ) {
    val cardinalityBuildBad1 = bd.byNameOrNull( TlaFiniteSetOper.cardinality.name )
    val cardinalityBuild = bd.byNameOrNull( TlaFiniteSetOper.cardinality.name, n_a )
    val cardinalityBuildBad2 = bd.byNameOrNull( TlaFiniteSetOper.cardinality.name, n_a, n_b, n_c )

    assert( cardinalityBuildBad1 == NullEx )
    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, n_a ) )
    assert( cardinalityBuildBad2 == NullEx )

    val isFiniteSetBuildBad1 = bd.byNameOrNull( TlaFiniteSetOper.isFiniteSet.name )
    val isFiniteSetBuild = bd.byNameOrNull( TlaFiniteSetOper.isFiniteSet.name, n_a )
    val isFiniteSetBuildBad2 = bd.byNameOrNull( TlaFiniteSetOper.isFiniteSet.name, n_a, n_b, n_c )

    assert( isFiniteSetBuildBad1 == NullEx )
    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, n_a ) )
    assert( isFiniteSetBuildBad2 == NullEx )

  }

  test( "Test direct methods: TlaFunOper" ) {
    val appBuild = bd.appFun( n_a, n_b )

    assert( appBuild == OperEx( TlaFunOper.app, n_a, n_b ) )

    val domainBuild = bd.dom( n_a )

    assert( domainBuild == OperEx( TlaFunOper.domain, n_a ) )

    val enumBuild1 = bd.enumFun( n_a, n_b )
    val enumBuild2 = bd.enumFun( n_a, n_b, n_c, n_d )

    assert( enumBuild1 == OperEx( TlaFunOper.enum, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.enumFun( n_a, n_b, n_c ) )
    assert( enumBuild2 == OperEx( TlaFunOper.enum, n_a, n_b, n_c, n_d ) )
    assertThrows[IllegalArgumentException]( bd.enumFun( n_a, n_b, n_c, n_d, n_e ) )

    val exceptBuild1 = bd.except( n_a, n_b, n_c )
    val exceptBuild2 = bd.except( n_a, n_b, n_c, n_d, n_e )

    assert( exceptBuild1 == OperEx( TlaFunOper.except, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.except( n_a, n_b, n_c, n_d ) )
    assert( exceptBuild2 == OperEx( TlaFunOper.except, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.except( n_a, n_b, n_c, n_d, n_e, n_f ) )

    val funDefBuild1 = bd.funDef( n_a, n_b, n_c )
    val funDefBuild2 = bd.funDef( n_a, n_b, n_c, n_d, n_e )

    assert( funDefBuild1 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.funDef( n_a, n_b, n_c, n_d ) )
    assert( funDefBuild2 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.funDef( n_a, n_b, n_c, n_d, n_e, n_f ) )

    val tupleBuild1 = bd.tuple()
    val tupleBuild2 = bd.tuple( n_a, n_b )

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, n_a, n_b ) )
  }

  test( "Test byName: TlaFunOper" ) {
    val appBuild = bd.byName( TlaFunOper.app.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.app.name, n_a ) )
    assert( appBuild == OperEx( TlaFunOper.app, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.app.name, n_a, n_b, n_c ) )

    val domainBuild = bd.byName( TlaFunOper.domain.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.domain.name ) )
    assert( domainBuild == OperEx( TlaFunOper.domain, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.domain.name, n_a, n_b, n_c ) )

    val enumBuild1 = bd.byName( TlaFunOper.enum.name, n_a, n_b )
    val enumBuild2 = bd.byName( TlaFunOper.enum.name, n_a, n_b, n_c, n_d )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.enum.name ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.enum.name, n_a ) )
    assert( enumBuild1 == OperEx( TlaFunOper.enum, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.enum.name, n_a, n_b, n_c ) )
    assert( enumBuild2 == OperEx( TlaFunOper.enum, n_a, n_b, n_c, n_d ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.enum.name, n_a, n_b, n_c, n_d, n_e ) )

    val exceptBuild1 = bd.byName( TlaFunOper.except.name, n_a, n_b, n_c )
    val exceptBuild2 = bd.byName( TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.except.name ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.except.name, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.except.name, n_a, n_b ) )
    assert( exceptBuild1 == OperEx( TlaFunOper.except, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.except.name, n_a, n_b, n_c, n_d ) )
    assert( exceptBuild2 == OperEx( TlaFunOper.except, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e, n_f ) )

    val funDefBuild1 = bd.byName( TlaFunOper.funDef.name, n_a, n_b, n_c )
    val funDefBuild2 = bd.byName( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e )

    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.funDef.name ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.funDef.name, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.funDef.name, n_a, n_b ) )
    assert( funDefBuild1 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d ) )
    assert( funDefBuild2 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e, n_f ) )

    val tupleBuild1 = bd.byName( TlaFunOper.tuple.name )
    val tupleBuild2 = bd.byName( TlaFunOper.tuple.name, n_a, n_b )

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, n_a, n_b ) )

  }

  test( "Test byNameOrNull: TlaFunOper" ) {
    val appBuildBad1 = bd.byNameOrNull( TlaFunOper.app.name, n_a )
    val appBuild = bd.byNameOrNull( TlaFunOper.app.name, n_a, n_b )
    val appBuildBad2 = bd.byNameOrNull( TlaFunOper.app.name, n_a, n_b, n_c )

    assert( appBuildBad1 == NullEx )
    assert( appBuild == OperEx( TlaFunOper.app, n_a, n_b ) )
    assert( appBuildBad2 == NullEx )

    val domainBuildBad1 = bd.byNameOrNull( TlaFunOper.domain.name )
    val domainBuild = bd.byNameOrNull( TlaFunOper.domain.name, n_a )
    val domainBuildBad2 = bd.byNameOrNull( TlaFunOper.domain.name, n_a, n_b, n_c )

    assert( domainBuildBad1 == NullEx )
    assert( domainBuild == OperEx( TlaFunOper.domain, n_a ) )
    assert( domainBuildBad2 == NullEx )

    val enumBuildEmpty = bd.byNameOrNull( TlaFunOper.enum.name )
    val enumBuild1 = bd.byNameOrNull( TlaFunOper.enum.name, n_a, n_b )
    val enumBuildBad1 = bd.byNameOrNull( TlaFunOper.enum.name, n_a, n_b, n_c )
    val enumBuild2 = bd.byNameOrNull( TlaFunOper.enum.name, n_a, n_b, n_c, n_d )
    val enumBuildBad2 = bd.byNameOrNull( TlaFunOper.enum.name, n_a, n_b, n_c, n_d, n_e )

    assert( enumBuildEmpty == NullEx )
    assert( enumBuild1 == OperEx( TlaFunOper.enum, n_a, n_b ) )
    assert( enumBuildBad1 == NullEx )
    assert( enumBuild2 == OperEx( TlaFunOper.enum, n_a, n_b, n_c, n_d ) )
    assert( enumBuildBad2 == NullEx )

    val exceptBuildEmpty = bd.byNameOrNull( TlaFunOper.except.name )
    val exceptBuildSingle = bd.byNameOrNull( TlaFunOper.except.name, n_a )
    val exceptBuildBad1 = bd.byNameOrNull( TlaFunOper.except.name, n_a, n_b )
    val exceptBuild1 = bd.byNameOrNull( TlaFunOper.except.name, n_a, n_b, n_c )
    val exceptBuildBad2 = bd.byNameOrNull( TlaFunOper.except.name, n_a, n_b, n_c, n_d )
    val exceptBuild2 = bd.byNameOrNull( TlaFunOper.except.name, n_a, n_b, n_c, n_d, n_e )

    assert( exceptBuildEmpty == NullEx )
    assert( exceptBuildSingle == NullEx )
    assert( exceptBuildBad1 == NullEx )
    assert( exceptBuild1 == OperEx( TlaFunOper.except, n_a, n_b, n_c ) )
    assert( exceptBuildBad2 == NullEx )
    assert( exceptBuild2 == OperEx( TlaFunOper.except, n_a, n_b, n_c, n_d, n_e ) )

    val funDefBuildEmpty = bd.byNameOrNull( TlaFunOper.funDef.name )
    val funDefBuildSingle = bd.byNameOrNull( TlaFunOper.funDef.name, n_a )
    val funDefBuildBad1 = bd.byNameOrNull( TlaFunOper.funDef.name, n_a, n_b )
    val funDefBuild1 = bd.byNameOrNull( TlaFunOper.funDef.name, n_a, n_b, n_c )
    val funDefBuildBad2 = bd.byNameOrNull( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d )
    val funDefBuild2 = bd.byNameOrNull( TlaFunOper.funDef.name, n_a, n_b, n_c, n_d, n_e )

    assert( funDefBuildEmpty == NullEx )
    assert( funDefBuildSingle == NullEx )
    assert( funDefBuildBad1 == NullEx )
    assert( funDefBuild1 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c ) )
    assert( funDefBuildBad2 == NullEx )
    assert( funDefBuild2 == OperEx( TlaFunOper.funDef, n_a, n_b, n_c, n_d, n_e ) )

    val tupleBuild1 = bd.byNameOrNull( TlaFunOper.tuple.name )
    val tupleBuild2 = bd.byNameOrNull( TlaFunOper.tuple.name, n_a, n_b )

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, n_a, n_b ) )
  }

  test( "Test direct methods: TlaSeqOper" ) {
    val appendBuild = bd.append( n_a, n_b )

    assert( appendBuild == OperEx( TlaSeqOper.append, n_a, n_b ) )

    val concatBuild = bd.concat( n_a, n_b )

    assert( concatBuild == OperEx( TlaSeqOper.concat, n_a, n_b ) )

    val headBuild = bd.head( n_a )

    assert( headBuild == OperEx( TlaSeqOper.head, n_a ) )

    val tailBuild = bd.tail( n_a )

    assert( tailBuild == OperEx( TlaSeqOper.tail, n_a ) )

    val lenBuild = bd.len( n_a )

    assert( lenBuild == OperEx( TlaSeqOper.len, n_a ) )
  }

  test( "Test byName: TlaSeqOper" ) {
    val appendBuild = bd.byName( TlaSeqOper.append.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.append.name, n_a ) )
    assert( appendBuild == OperEx( TlaSeqOper.append, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.append.name, n_a, n_b, n_c ) )

    val concatBuild = bd.byName( TlaSeqOper.concat.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.concat.name, n_a ) )
    assert( concatBuild == OperEx( TlaSeqOper.concat, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.concat.name, n_a, n_b, n_c ) )

    val headBuild = bd.byName( TlaSeqOper.head.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.head.name ) )
    assert( headBuild == OperEx( TlaSeqOper.head, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.head.name, n_a, n_b ) )

    val tailBuild = bd.byName( TlaSeqOper.tail.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.tail.name ) )
    assert( tailBuild == OperEx( TlaSeqOper.tail, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.tail.name, n_a, n_b ) )

    val lenBuild = bd.byName( TlaSeqOper.len.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.len.name ) )
    assert( lenBuild == OperEx( TlaSeqOper.len, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSeqOper.len.name, n_a, n_b ) )
  }

  test( "Test byNameOrNull: TlaSeqOper" ) {
    val appendBuildBad1 = bd.byNameOrNull( TlaSeqOper.append.name, n_a )
    val appendBuild = bd.byNameOrNull( TlaSeqOper.append.name, n_a, n_b )
    val appendBuildBad2 = bd.byNameOrNull( TlaSeqOper.append.name, n_a, n_b, n_c )

    assert( appendBuildBad1 == NullEx )
    assert( appendBuild == OperEx( TlaSeqOper.append, n_a, n_b ) )
    assert( appendBuildBad2 == NullEx )

    val concatBuildBad1 = bd.byNameOrNull( TlaSeqOper.concat.name, n_a )
    val concatBuild = bd.byNameOrNull( TlaSeqOper.concat.name, n_a, n_b )
    val concatBuildBad2 = bd.byNameOrNull( TlaSeqOper.concat.name, n_a, n_b, n_c )

    assert( concatBuildBad1 == NullEx )
    assert( concatBuild == OperEx( TlaSeqOper.concat, n_a, n_b ) )
    assert( concatBuildBad2 == NullEx )

    val headBuildBad1 = bd.byNameOrNull( TlaSeqOper.head.name )
    val headBuild = bd.byNameOrNull( TlaSeqOper.head.name, n_a )
    val headBuildBad2 = bd.byNameOrNull( TlaSeqOper.head.name, n_a, n_b )

    assert( headBuildBad1 == NullEx )
    assert( headBuild == OperEx( TlaSeqOper.head, n_a ) )
    assert( headBuildBad2 == NullEx )

    val tailBuildBad1 = bd.byNameOrNull( TlaSeqOper.tail.name )
    val tailBuild = bd.byNameOrNull( TlaSeqOper.tail.name, n_a )
    val tailBuildBad2 = bd.byNameOrNull( TlaSeqOper.tail.name, n_a, n_b )

    assert( tailBuildBad1 == NullEx )
    assert( tailBuild == OperEx( TlaSeqOper.tail, n_a ) )
    assert( tailBuildBad2 == NullEx )

    val lenBuildBad1 = bd.byNameOrNull( TlaSeqOper.len.name )
    val lenBuild = bd.byNameOrNull( TlaSeqOper.len.name, n_a )
    val lenBuildBad2 = bd.byNameOrNull( TlaSeqOper.len.name, n_a, n_b )

    assert( lenBuildBad1 == NullEx )
    assert( lenBuild == OperEx( TlaSeqOper.len, n_a ) )
    assert( lenBuildBad2 == NullEx )
  }

  test( "Test direct methods: TlaSetOper" ) {
    val enumSetBuild1 = bd.enumSet()
    val enumSetBuild2 = bd.enumSet( n_a, n_b )

    assert( enumSetBuild1 == OperEx( TlaSetOper.enumSet ) )
    assert( enumSetBuild2 == OperEx( TlaSetOper.enumSet, n_a, n_b ) )

    val inBuild = bd.in( n_a, n_b )

    assert( inBuild == OperEx( TlaSetOper.in, n_a, n_b ) )

    val notinBuild = bd.notin( n_a, n_b )

    assert( notinBuild == OperEx( TlaSetOper.notin, n_a, n_b ) )

    val capBuild = bd.cap( n_a, n_b )

    assert( capBuild == OperEx( TlaSetOper.cap, n_a, n_b ) )

    val cupBuild = bd.cup( n_a, n_b )

    assert( cupBuild == OperEx( TlaSetOper.cup, n_a, n_b ) )

    val unionBuild = bd.union( n_a )

    assert( unionBuild == OperEx( TlaSetOper.union, n_a ) )

    val filterBuild = bd.filter( n_a, n_b, n_c )

    assert( filterBuild == OperEx( TlaSetOper.filter, n_a, n_b, n_c ) )

    val mapBuild1 = bd.map( n_a, n_b, n_c )
    val mapBuild2 = bd.map( n_a, n_b, n_c, n_d, n_e )

    assert( mapBuild1 == OperEx( TlaSetOper.map, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.map( n_a, n_b, n_c, n_d ) )
    assert( mapBuild2 == OperEx( TlaSetOper.map, n_a, n_b, n_c, n_d, n_e ) )
    assertThrows[IllegalArgumentException]( bd.map( n_a, n_b, n_c, n_d, n_e, n_f ) )

    val funSetBuild = bd.funSet( n_a, n_b )

    assert( funSetBuild == OperEx( TlaSetOper.funSet, n_a, n_b ) )

    val recSetBuild1 = bd.recSet()
    val recSetBuild2 = bd.recSet( n_a, n_b )

    assert( recSetBuild1 == OperEx( TlaSetOper.recSet ) )
    assertThrows[IllegalArgumentException]( bd.recSet( n_a ) )
    assert( recSetBuild2 == OperEx( TlaSetOper.recSet, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.recSet( n_a, n_b, n_c ) )

    val seqSetBuild = bd.seqSet( n_a )

    assert( seqSetBuild == OperEx( TlaSetOper.seqSet, n_a ) )

    val subsetBuild = bd.subset( n_a, n_b )

    assert( subsetBuild == OperEx( TlaSetOper.subsetProper, n_a, n_b ) )

    val subseteqBuild = bd.subseteq( n_a, n_b )

    assert( subseteqBuild == OperEx( TlaSetOper.subseteq, n_a, n_b ) )

    val supsetBuild = bd.supset( n_a, n_b )

    assert( supsetBuild == OperEx( TlaSetOper.supsetProper, n_a, n_b ) )

    val supseteqBuild = bd.supseteq( n_a, n_b )

    assert( supseteqBuild == OperEx( TlaSetOper.supseteq, n_a, n_b ) )

    val setminusBuild = bd.setminus( n_a, n_b )

    assert( setminusBuild == OperEx( TlaSetOper.setminus, n_a, n_b ) )

    val timesBuild1 = bd.times()
    val timesBuild2 = bd.times( n_a, n_b )

    assert( timesBuild1 == OperEx( TlaSetOper.times ) )
    assert( timesBuild2 == OperEx( TlaSetOper.times, n_a, n_b ) )

    val powSetBuild = bd.powSet( n_a )

    assert( powSetBuild == OperEx( TlaSetOper.powerset, n_a ) )
  }

  test( "Test byName: TlaSetOper" ) {
    val enumSetBuild1 = bd.byName( TlaSetOper.enumSet.name )
    val enumSetBuild2 = bd.byName( TlaSetOper.enumSet.name, n_a, n_b )

    assert( enumSetBuild1 == OperEx( TlaSetOper.enumSet ) )
    assert( enumSetBuild2 == OperEx( TlaSetOper.enumSet, n_a, n_b ) )

    val inBuild = bd.byName( TlaSetOper.in.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.in.name, n_a ) )
    assert( inBuild == OperEx( TlaSetOper.in, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.in.name, n_a, n_b, n_c ) )

    val notinBuild = bd.byName( TlaSetOper.notin.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.notin.name, n_a ) )
    assert( notinBuild == OperEx( TlaSetOper.notin, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.notin.name, n_a, n_b, n_c ) )

    val capBuild = bd.byName( TlaSetOper.cap.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.cap.name, n_a ) )
    assert( capBuild == OperEx( TlaSetOper.cap, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.cap.name, n_a, n_b, n_c ) )

    val cupBuild = bd.byName( TlaSetOper.cup.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.cup.name, n_a ) )
    assert( cupBuild == OperEx( TlaSetOper.cup, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.cup.name, n_a, n_b, n_c ) )

    val unionBuild = bd.byName( TlaSetOper.union.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.union.name ) )
    assert( unionBuild == OperEx( TlaSetOper.union, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.union.name, n_a, n_b ) )

    val filterBuild = bd.byName( TlaSetOper.filter.name, n_a, n_b, n_c )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.filter.name, n_a, n_b ) )
    assert( filterBuild == OperEx( TlaSetOper.filter, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.filter.name, n_a, n_b, n_c, n_d ) )

    val mapBuild1 = bd.byNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c )
    val mapBuild2 = bd.byNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c, n_d, n_e )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.map.name, n_a, n_b ) )
    assert( mapBuild1 == OperEx( TlaSetOper.map, n_a, n_b, n_c ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.map.name, n_a, n_b, n_c, n_d ) )
    assert( mapBuild2 == OperEx( TlaSetOper.map, n_a, n_b, n_c, n_d, n_e ) )

    val funSetBuild = bd.byName( TlaSetOper.funSet.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.funSet.name, n_a ) )
    assert( funSetBuild == OperEx( TlaSetOper.funSet, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.funSet.name, n_a, n_b, n_c ) )

    val recSetBuild1 = bd.byNameOrNull( TlaSetOper.recSet.name )
    val recSetBuild2 = bd.byNameOrNull( TlaSetOper.recSet.name, n_a, n_b )

    assert( recSetBuild1 == OperEx( TlaSetOper.recSet ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.recSet.name, n_a ) )
    assert( recSetBuild2 == OperEx( TlaSetOper.recSet, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.recSet.name, n_a, n_b, n_c ) )

    val seqSetBuild = bd.byName( TlaSetOper.seqSet.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.seqSet.name ) )
    assert( seqSetBuild == OperEx( TlaSetOper.seqSet, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.seqSet.name, n_a, n_b ) )

    val subsetBuild = bd.byName( TlaSetOper.subsetProper.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.subsetProper.name, n_a ) )
    assert( subsetBuild == OperEx( TlaSetOper.subsetProper, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.subsetProper.name, n_a, n_b, n_c ) )

    val subseteqBuild = bd.byName( TlaSetOper.subseteq.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.subseteq.name, n_a ) )
    assert( subseteqBuild == OperEx( TlaSetOper.subseteq, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.subseteq.name, n_a, n_b, n_c ) )

    val supsetBuild = bd.byName( TlaSetOper.supsetProper.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.supsetProper.name, n_a ) )
    assert( supsetBuild == OperEx( TlaSetOper.supsetProper, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.supsetProper.name, n_a, n_b, n_c ) )

    val supseteqBuild = bd.byName( TlaSetOper.supseteq.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.supseteq.name, n_a ) )
    assert( supseteqBuild == OperEx( TlaSetOper.supseteq, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.supseteq.name, n_a, n_b, n_c ) )

    val setminusBuild = bd.byName( TlaSetOper.setminus.name, n_a, n_b )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.setminus.name, n_a ) )
    assert( setminusBuild == OperEx( TlaSetOper.setminus, n_a, n_b ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.setminus.name, n_a, n_b, n_c ) )

    val timesBuild1 = bd.byName( TlaSetOper.times.name )
    val timesBuild2 = bd.byName( TlaSetOper.times.name, n_a, n_b )

    assert( timesBuild1 == OperEx( TlaSetOper.times ) )
    assert( timesBuild2 == OperEx( TlaSetOper.times, n_a, n_b ) )

    val powSetBuild = bd.byName( TlaSetOper.powerset.name, n_a )

    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.powerset.name ) )
    assert( powSetBuild == OperEx( TlaSetOper.powerset, n_a ) )
    assertThrows[IllegalArgumentException]( bd.byName( TlaSetOper.powerset.name, n_a, n_b ) )

  }

  test( "Test byNameOrNull: TlaSetOper" ) {
    val enumSetBuild1 = bd.byNameOrNull( TlaSetOper.enumSet.name )
    val enumSetBuild2 = bd.byNameOrNull( TlaSetOper.enumSet.name, n_a, n_b )

    assert( enumSetBuild1 == OperEx( TlaSetOper.enumSet ) )
    assert( enumSetBuild2 == OperEx( TlaSetOper.enumSet, n_a, n_b ) )

    val inBuildBad1 = bd.byNameOrNull( TlaSetOper.in.name, n_a )
    val inBuild = bd.byNameOrNull( TlaSetOper.in.name, n_a, n_b )
    val inBuildBad2 = bd.byNameOrNull( TlaSetOper.in.name, n_a, n_b, n_c )

    assert( inBuildBad1 == NullEx )
    assert( inBuild == OperEx( TlaSetOper.in, n_a, n_b ) )
    assert( inBuildBad2 == NullEx )

    val notinBuildBad1 = bd.byNameOrNull( TlaSetOper.notin.name, n_a )
    val notinBuild = bd.byNameOrNull( TlaSetOper.notin.name, n_a, n_b )
    val notinBuildBad2 = bd.byNameOrNull( TlaSetOper.notin.name, n_a, n_b, n_c )

    assert( notinBuildBad1 == NullEx )
    assert( notinBuild == OperEx( TlaSetOper.notin, n_a, n_b ) )
    assert( notinBuildBad2 == NullEx )

    val capBuildBad1 = bd.byNameOrNull( TlaSetOper.cap.name, n_a )
    val capBuild = bd.byNameOrNull( TlaSetOper.cap.name, n_a, n_b )
    val capBuildBad2 = bd.byNameOrNull( TlaSetOper.cap.name, n_a, n_b, n_c )

    assert( capBuildBad1 == NullEx )
    assert( capBuild == OperEx( TlaSetOper.cap, n_a, n_b ) )
    assert( capBuildBad2 == NullEx )

    val cupBuildBad1 = bd.byNameOrNull( TlaSetOper.cup.name, n_a )
    val cupBuild = bd.byNameOrNull( TlaSetOper.cup.name, n_a, n_b )
    val cupBuildBad2 = bd.byNameOrNull( TlaSetOper.cup.name, n_a, n_b, n_c )

    assert( cupBuildBad1 == NullEx )
    assert( cupBuild == OperEx( TlaSetOper.cup, n_a, n_b ) )
    assert( cupBuildBad2 == NullEx )

    val unionBuildBad1 = bd.byNameOrNull( TlaSetOper.union.name )
    val unionBuild = bd.byNameOrNull( TlaSetOper.union.name, n_a )
    val unionBuildBad2 = bd.byNameOrNull( TlaSetOper.union.name, n_a, n_b )

    assert( unionBuildBad1 == NullEx )
    assert( unionBuild == OperEx( TlaSetOper.union, n_a ) )
    assert( unionBuildBad2 == NullEx )

    val filterBuildBad1 = bd.byNameOrNull( TlaSetOper.filter.name, n_a, n_b )
    val filterBuild = bd.byNameOrNull( TlaSetOper.filter.name, n_a, n_b, n_c )
    val filterBuildBad2 = bd.byNameOrNull( TlaSetOper.filter.name, n_a, n_b, n_c, n_d )

    assert( filterBuildBad1 == NullEx )
    assert( filterBuild == OperEx( TlaSetOper.filter, n_a, n_b, n_c ) )
    assert( filterBuildBad2 == NullEx )

    val mapBuildBad1 = bd.byNameOrNull( TlaSetOper.map.name, n_a, n_b )
    val mapBuild1 = bd.byNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c )
    val mapBuildBad2 = bd.byNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c, n_d )
    val mapBuild2 = bd.byNameOrNull( TlaSetOper.map.name, n_a, n_b, n_c, n_d, n_e )

    assert( mapBuildBad1 == NullEx )
    assert( mapBuild1 == OperEx( TlaSetOper.map, n_a, n_b, n_c ) )
    assert( mapBuildBad2 == NullEx )
    assert( mapBuild2 == OperEx( TlaSetOper.map, n_a, n_b, n_c, n_d, n_e ) )

    val funSetBuildBad1 = bd.byNameOrNull( TlaSetOper.funSet.name, n_a )
    val funSetBuild = bd.byNameOrNull( TlaSetOper.funSet.name, n_a, n_b )
    val funSetBuildBad2 = bd.byNameOrNull( TlaSetOper.funSet.name, n_a, n_b, n_c )

    assert( funSetBuildBad1 == NullEx )
    assert( funSetBuild == OperEx( TlaSetOper.funSet, n_a, n_b ) )
    assert( funSetBuildBad2 == NullEx )

    val recSetBuild1 = bd.byNameOrNull( TlaSetOper.recSet.name )
    val recSetBuildBad1 = bd.byNameOrNull( TlaSetOper.recSet.name, n_a )
    val recSetBuild2 = bd.byNameOrNull( TlaSetOper.recSet.name, n_a, n_b )
    val recSetBuildBad2 = bd.byNameOrNull( TlaSetOper.recSet.name, n_a, n_b, n_c )

    assert( recSetBuild1 == OperEx( TlaSetOper.recSet ) )
    assert( recSetBuildBad1 == NullEx )
    assert( recSetBuild2 == OperEx( TlaSetOper.recSet, n_a, n_b ) )
    assert( recSetBuildBad2 == NullEx )

    val seqSetBuildBad1 = bd.byNameOrNull( TlaSetOper.seqSet.name )
    val seqSetBuild = bd.byNameOrNull( TlaSetOper.seqSet.name, n_a )
    val seqSetBuildBad2 = bd.byNameOrNull( TlaSetOper.seqSet.name, n_a, n_b )

    assert( seqSetBuildBad1 == NullEx )
    assert( seqSetBuild == OperEx( TlaSetOper.seqSet, n_a ) )
    assert( seqSetBuildBad2 == NullEx )

    val subsetBuildBad1 = bd.byNameOrNull( TlaSetOper.subsetProper.name, n_a )
    val subsetBuild = bd.byNameOrNull( TlaSetOper.subsetProper.name, n_a, n_b )
    val subsetBuildBad2 = bd.byNameOrNull( TlaSetOper.subsetProper.name, n_a, n_b, n_c )

    assert( subsetBuildBad1 == NullEx )
    assert( subsetBuild == OperEx( TlaSetOper.subsetProper, n_a, n_b ) )
    assert( subsetBuildBad2 == NullEx )

    val subseteqBuildBad1 = bd.byNameOrNull( TlaSetOper.subseteq.name, n_a )
    val subseteqBuild = bd.byNameOrNull( TlaSetOper.subseteq.name, n_a, n_b )
    val subseteqBuildBad2 = bd.byNameOrNull( TlaSetOper.subseteq.name, n_a, n_b, n_c )

    assert( subseteqBuildBad1 == NullEx )
    assert( subseteqBuild == OperEx( TlaSetOper.subseteq, n_a, n_b ) )
    assert( subseteqBuildBad2 == NullEx )

    val supsetBuildBad1 = bd.byNameOrNull( TlaSetOper.supsetProper.name, n_a )
    val supsetBuild = bd.byNameOrNull( TlaSetOper.supsetProper.name, n_a, n_b )
    val supsetBuildBad2 = bd.byNameOrNull( TlaSetOper.supsetProper.name, n_a, n_b, n_c )

    assert( supsetBuildBad1 == NullEx )
    assert( supsetBuild == OperEx( TlaSetOper.supsetProper, n_a, n_b ) )
    assert( supsetBuildBad2 == NullEx )

    val supseteqBuildBad1 = bd.byNameOrNull( TlaSetOper.supseteq.name, n_a )
    val supseteqBuild = bd.byNameOrNull( TlaSetOper.supseteq.name, n_a, n_b )
    val supseteqBuildBad2 = bd.byNameOrNull( TlaSetOper.supseteq.name, n_a, n_b, n_c )

    assert( supseteqBuildBad1 == NullEx )
    assert( supseteqBuild == OperEx( TlaSetOper.supseteq, n_a, n_b ) )
    assert( supseteqBuildBad2 == NullEx )

    val setminusBuildBad1 = bd.byNameOrNull( TlaSetOper.setminus.name, n_a )
    val setminusBuild = bd.byNameOrNull( TlaSetOper.setminus.name, n_a, n_b )
    val setminusBuildBad2 = bd.byNameOrNull( TlaSetOper.setminus.name, n_a, n_b, n_c )

    assert( setminusBuildBad1 == NullEx )
    assert( setminusBuild == OperEx( TlaSetOper.setminus, n_a, n_b ) )
    assert( setminusBuildBad2 == NullEx )

    val timesBuild1 = bd.byNameOrNull( TlaSetOper.times.name )
    val timesBuild2 = bd.byNameOrNull( TlaSetOper.times.name, n_a, n_b )

    assert( timesBuild1 == OperEx( TlaSetOper.times ) )
    assert( timesBuild2 == OperEx( TlaSetOper.times, n_a, n_b ) )

    val powersetBuildBad1 = bd.byNameOrNull( TlaSetOper.powerset.name )
    val powersetBuild = bd.byNameOrNull( TlaSetOper.powerset.name, n_a )
    val powersetBuildBad2 = bd.byNameOrNull( TlaSetOper.powerset.name, n_a, n_b )

    assert( powersetBuildBad1 == NullEx )
    assert( powersetBuild == OperEx( TlaSetOper.powerset, n_a ) )
    assert( powersetBuildBad2 == NullEx )

  }

}

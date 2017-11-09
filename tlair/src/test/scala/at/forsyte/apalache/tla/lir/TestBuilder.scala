package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestBuilder extends FunSuite {
  test( "Test garbage" ){
    val garbage = Builder.oper("a string that is obviously not an operator name", NullEx, NameEx("arg2"))
    assert(garbage == NullEx)
  }

  test( "Test TlaOper" ){
    val eqBuildBad1 = Builder.oper(TlaOper.eq.name, NameEx("a"))
    val eqBuild = Builder.oper(TlaOper.eq.name, NameEx("a"), NameEx("b"))
    val eqBuildBad2 = Builder.oper(TlaOper.eq.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert(eqBuildBad1 == NullEx)
    assert(eqBuild == OperEx( TlaOper.eq, NameEx("a"), NameEx("b") ))
    assert(eqBuildBad2 == NullEx)

    val neBuildBad1 = Builder.oper(TlaOper.ne.name, NameEx("a"))
    val neBuild = Builder.oper(TlaOper.ne.name, NameEx("a"), NameEx("b"))
    val neBuildBad2 = Builder.oper(TlaOper.ne.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert(neBuildBad1 == NullEx)
    assert(neBuild == OperEx( TlaOper.ne, NameEx("a"), NameEx("b") ))
    assert(neBuildBad2 == NullEx)

    val cbBuildBad1 = Builder.oper(TlaOper.chooseBounded.name, NameEx("a"), NameEx("b"))
    val cbBuild = Builder.oper(TlaOper.chooseBounded.name, NameEx("a"), NameEx("b"), NameEx("c"))
    val cbBuildBad2 = Builder.oper(TlaOper.chooseBounded.name, NameEx("a"), NameEx("b"), NameEx("c"), NameEx("d"))

    assert(cbBuildBad1 == NullEx)
    assert(cbBuild == OperEx( TlaOper.chooseBounded, NameEx("a"), NameEx("b"), NameEx("c") ))
    assert(cbBuildBad2 == NullEx)

    val cubBuild = Builder.oper(TlaOper.chooseUnbounded.name, NameEx("a"), NameEx("b"))
    val cubBuildBad1 = Builder.oper(TlaOper.chooseUnbounded.name, NameEx("a"), NameEx("b"), NameEx("c"))
    val cubBuildBad2 = Builder.oper(TlaOper.chooseUnbounded.name, NameEx("a"), NameEx("b"), NameEx("c"), NameEx("d"))

    assert(cubBuild == OperEx( TlaOper.chooseUnbounded, NameEx("a"), NameEx("b") ))
    assert(cubBuildBad1 == NullEx)
    assert(cubBuildBad2 == NullEx)
  }

  test("Test TlaActionOper"){

    val primeBuildBad1 = Builder.oper( TlaActionOper.prime.name )
    val primeBuild = Builder.oper( TlaActionOper.prime.name, NameEx("a") )
    val primeBuildBad2 = Builder.oper( TlaActionOper.prime.name, NameEx("a"), NameEx("b") )

    assert(primeBuildBad1 == NullEx)
    assert(primeBuild == OperEx( TlaActionOper.prime, NameEx("a") ))
    assert(primeBuildBad2 == NullEx)

    val stutterBuildBad1 = Builder.oper( TlaActionOper.stutter.name, NameEx("A") )
    val stutterBuild = Builder.oper( TlaActionOper.stutter.name, NameEx("A"), NameEx("e") )
    val stutterBuildBad2 = Builder.oper( TlaActionOper.stutter.name, NameEx("A"), NameEx("e"), NameEx("?") )

    assert(stutterBuildBad1 == NullEx)
    assert(stutterBuild == OperEx( TlaActionOper.stutter, NameEx("A"), NameEx("e") ))
    assert(stutterBuildBad2 == NullEx)

    val nostutterBuildBad1 = Builder.oper( TlaActionOper.nostutter.name, NameEx("A"))
    val nostutterBuild = Builder.oper( TlaActionOper.nostutter.name, NameEx("A"), NameEx("e") )
    val nostutterBuildBad2 = Builder.oper( TlaActionOper.nostutter.name, NameEx("A"), NameEx("e"), NameEx("?") )

    assert(nostutterBuildBad1 == NullEx)
    assert(nostutterBuild == OperEx( TlaActionOper.nostutter, NameEx("A"), NameEx("e") ))
    assert(nostutterBuildBad2 == NullEx)

    val enabledBuildBad1 = Builder.oper( TlaActionOper.enabled.name )
    val enabledBuild = Builder.oper( TlaActionOper.enabled.name, NameEx("A") )
    val enabledBuildBad2 = Builder.oper( TlaActionOper.enabled.name, NameEx("A"), NameEx("b") )

    assert(enabledBuildBad1 == NullEx)
    assert(enabledBuild == OperEx( TlaActionOper.enabled, NameEx("A") ))
    assert(enabledBuildBad2 == NullEx)

    val unchangedBuildBad1 = Builder.oper( TlaActionOper.unchanged.name )
    val unchangedBuild = Builder.oper( TlaActionOper.unchanged.name, NameEx("A") )
    val unchangedBuildBad2 = Builder.oper( TlaActionOper.unchanged.name, NameEx("A"), NameEx("b") )

    assert(unchangedBuildBad1 == NullEx)
    assert(unchangedBuild == OperEx( TlaActionOper.unchanged, NameEx("A") ))
    assert(unchangedBuildBad2 == NullEx)

    val compositionBuildBad1 = Builder.oper( TlaActionOper.composition.name, NameEx("A"))
    val compositionBuild = Builder.oper( TlaActionOper.composition.name, NameEx("A"), NameEx("B") )
    val compositionBuildBad2 = Builder.oper( TlaActionOper.composition.name, NameEx("A"), NameEx("B"), NameEx("?") )

    assert(compositionBuildBad1 == NullEx)
    assert(compositionBuild == OperEx( TlaActionOper.composition, NameEx("A"), NameEx("B") ))
    assert(compositionBuildBad2 == NullEx)

  }

  test("Test TlaControlOper") {

    val caseNoOtherBuildEmpty = Builder.oper(TlaControlOper.caseNoOther.name)
    val caseNoOtherBuild = Builder.oper(TlaControlOper.caseNoOther.name, NameEx("a"), NameEx("b"))
    val caseNoOtherBuildBad = Builder.oper(TlaControlOper.caseNoOther.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(caseNoOtherBuildEmpty == NullEx )
    assert(caseNoOtherBuild == OperEx( TlaControlOper.caseNoOther, NameEx("a"), NameEx("b") ) )
    assert(caseNoOtherBuildBad == NullEx )

    val caseWithOtherBuildEmpty = Builder.oper(TlaControlOper.caseWithOther.name)
    val caseWithOtherBuildSingle = Builder.oper(TlaControlOper.caseWithOther.name, NameEx("a"))
    val caseWithOtherBuildBad = Builder.oper(TlaControlOper.caseWithOther.name, NameEx("a"), NameEx("b"))
    val caseWithOtherBuild = Builder.oper(TlaControlOper.caseWithOther.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(caseWithOtherBuildEmpty == NullEx )
    assert(caseWithOtherBuildSingle == NullEx )
    assert(caseWithOtherBuildBad == NullEx )
    assert(caseWithOtherBuild == OperEx( TlaControlOper.caseWithOther, NameEx("a"), NameEx("b"), NameEx("c") ) )

    val iteBuildBad1 = Builder.oper(TlaControlOper.ifThenElse.name, NameEx("a"), NameEx("b") )
    val iteBuild = Builder.oper(TlaControlOper.ifThenElse.name, NameEx("a"), NameEx("b"), NameEx("c") )
    val iteBuildBad2 = Builder.oper(TlaControlOper.ifThenElse.name, NameEx("a"), NameEx("b"), NameEx("c"), NameEx("d") )

    assert(iteBuildBad1 == NullEx )
    assert(iteBuild == OperEx( TlaControlOper.ifThenElse, NameEx("a"), NameEx("b"), NameEx("c") ) )
    assert(iteBuildBad2 == NullEx )
  }

  test("Test TlaTempOper"){

    val AABuildBad1 = Builder.oper(TlaTempOper.AA.name, NameEx("a") )
    val AABuild = Builder.oper(TlaTempOper.AA.name, NameEx("a"), NameEx("b") )
    val AABuildBad2 = Builder.oper(TlaTempOper.AA.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( AABuildBad1 == NullEx )
    assert( AABuild == OperEx( TlaTempOper.AA, NameEx("a"), NameEx("b") ))
    assert( AABuildBad2 == NullEx )

    val EEBuildBad1 = Builder.oper(TlaTempOper.EE.name, NameEx("a") )
    val EEBuild = Builder.oper(TlaTempOper.EE.name, NameEx("a"), NameEx("b") )
    val EEBuildBad2 = Builder.oper(TlaTempOper.EE.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( EEBuildBad1 == NullEx )
    assert( EEBuild == OperEx( TlaTempOper.EE, NameEx("a"), NameEx("b") ))
    assert( EEBuildBad2 == NullEx )

    val boxBuildBad1 = Builder.oper(TlaTempOper.box.name )
    val boxBuild = Builder.oper(TlaTempOper.box.name, NameEx("a"))
    val boxBuildBad2 = Builder.oper(TlaTempOper.box.name, NameEx("a"), NameEx("b"))

    assert( boxBuildBad1 == NullEx )
    assert( boxBuild == OperEx( TlaTempOper.box, NameEx("a") ))
    assert( boxBuildBad2 == NullEx )

    val diamondBuildBad1 = Builder.oper(TlaTempOper.diamond.name )
    val diamondBuild = Builder.oper(TlaTempOper.diamond.name, NameEx("a"))
    val diamondBuildBad2 = Builder.oper(TlaTempOper.diamond.name, NameEx("a"), NameEx("b"))

    assert( diamondBuildBad1 == NullEx )
    assert( diamondBuild == OperEx( TlaTempOper.diamond, NameEx("a") ))
    assert( diamondBuildBad2 == NullEx )

    val leadsToBuildBad1 = Builder.oper(TlaTempOper.leadsTo.name, NameEx("a") )
    val leadsToBuild = Builder.oper(TlaTempOper.leadsTo.name, NameEx("a"), NameEx("b") )
    val leadsToBuildBad2 = Builder.oper(TlaTempOper.leadsTo.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( leadsToBuildBad1 == NullEx )
    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, NameEx("a"), NameEx("b") ))
    assert( leadsToBuildBad2 == NullEx )

    val guaranteesBuildBad1 = Builder.oper(TlaTempOper.guarantees.name, NameEx("a") )
    val guaranteesBuild = Builder.oper(TlaTempOper.guarantees.name, NameEx("a"), NameEx("b") )
    val guaranteesBuildBad2 = Builder.oper(TlaTempOper.guarantees.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( guaranteesBuildBad1 == NullEx )
    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, NameEx("a"), NameEx("b") ))
    assert( guaranteesBuildBad2 == NullEx )


    val strongFairnessBuildBad1 = Builder.oper(TlaTempOper.strongFairness.name, NameEx("a") )
    val strongFairnessBuild = Builder.oper(TlaTempOper.strongFairness.name, NameEx("a"), NameEx("b") )
    val strongFairnessBuildBad2 = Builder.oper(TlaTempOper.strongFairness.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( strongFairnessBuildBad1 == NullEx )
    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, NameEx("a"), NameEx("b") ))
    assert( strongFairnessBuildBad2 == NullEx )

    val weakFairnessBuildBad1 = Builder.oper(TlaTempOper.weakFairness.name, NameEx("a") )
    val weakFairnessBuild = Builder.oper(TlaTempOper.weakFairness.name, NameEx("a"), NameEx("b") )
    val weakFairnessBuildBad2 = Builder.oper(TlaTempOper.weakFairness.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( weakFairnessBuildBad1 == NullEx )
    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, NameEx("a"), NameEx("b") ))
    assert( weakFairnessBuildBad2 == NullEx )
//    TlaTempOper.strongFairness.name -> TlaTempOper.strongFairness,
//    TlaTempOper.weakFairness.name   -> TlaTempOper.weakFairness,
  }

  test("Test TlaArithOper"){

    val sumBuild1 = Builder.oper(TlaArithOper.sum.name)
    val sumBuild2 = Builder.oper(TlaArithOper.sum.name, NameEx("a"), NameEx("b"))

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, NameEx("a"),NameEx("b") ) )

    val plusBuildBad1 = Builder.oper(TlaArithOper.plus.name, NameEx("a") )
    val plusBuild = Builder.oper(TlaArithOper.plus.name, NameEx("a"), NameEx("b"))
    val plusBuildBad2 = Builder.oper(TlaArithOper.plus.name, NameEx("a"), NameEx("b"), NameEx("c"))
    
    assert( plusBuildBad1 == NullEx )
    assert( plusBuild == OperEx( TlaArithOper.plus, NameEx("a"),NameEx("b") ) )
    assert( plusBuildBad2 == NullEx )

    val minusBuildBad1 = Builder.oper(TlaArithOper.minus.name, NameEx("a") )
    val minusBuild = Builder.oper(TlaArithOper.minus.name, NameEx("a"), NameEx("b"))
    val minusBuildBad2 = Builder.oper(TlaArithOper.minus.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( minusBuildBad1 == NullEx )
    assert( minusBuild == OperEx( TlaArithOper.minus, NameEx("a"),NameEx("b") ) )
    assert( minusBuildBad2 == NullEx )

    val uminusBuildBad1 = Builder.oper(TlaArithOper.uminus.name )
    val uminusBuild = Builder.oper(TlaArithOper.uminus.name, NameEx("a"))
    val uminusBuildBad2 = Builder.oper(TlaArithOper.uminus.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( uminusBuildBad1 == NullEx )
    assert( uminusBuild == OperEx( TlaArithOper.uminus, NameEx("a") ) )
    assert( uminusBuildBad2 == NullEx )

    val prodBuild1 = Builder.oper(TlaArithOper.prod.name)
    val prodBuild2 = Builder.oper(TlaArithOper.prod.name, NameEx("a"), NameEx("b"))

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, NameEx("a"),NameEx("b") ) )

    val multBuildBad1 = Builder.oper(TlaArithOper.mult.name, NameEx("a") )
    val multBuild = Builder.oper(TlaArithOper.mult.name, NameEx("a"), NameEx("b"))
    val multBuildBad2 = Builder.oper(TlaArithOper.mult.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( multBuildBad1 == NullEx )
    assert( multBuild == OperEx( TlaArithOper.mult, NameEx("a"),NameEx("b") ) )
    assert( multBuildBad2 == NullEx )

    val divBuildBad1 = Builder.oper(TlaArithOper.div.name, NameEx("a") )
    val divBuild = Builder.oper(TlaArithOper.div.name, NameEx("a"), NameEx("b"))
    val divBuildBad2 = Builder.oper(TlaArithOper.div.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( divBuildBad1 == NullEx )
    assert( divBuild == OperEx( TlaArithOper.div, NameEx("a"),NameEx("b") ) )
    assert( divBuildBad2 == NullEx )

    val modBuildBad1 = Builder.oper(TlaArithOper.mod.name, NameEx("a") )
    val modBuild = Builder.oper(TlaArithOper.mod.name, NameEx("a"), NameEx("b"))
    val modBuildBad2 = Builder.oper(TlaArithOper.mod.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( modBuildBad1 == NullEx )
    assert( modBuild == OperEx( TlaArithOper.mod, NameEx("a"),NameEx("b") ) )
    assert( modBuildBad2 == NullEx )

    val realDivBuildBad1 = Builder.oper(TlaArithOper.realDiv.name, NameEx("a") )
    val realDivBuild = Builder.oper(TlaArithOper.realDiv.name, NameEx("a"), NameEx("b"))
    val realDivBuildBad2 = Builder.oper(TlaArithOper.realDiv.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( realDivBuildBad1 == NullEx )
    assert( realDivBuild == OperEx( TlaArithOper.realDiv, NameEx("a"),NameEx("b") ) )
    assert( realDivBuildBad2 == NullEx )

    val expBuildBad1 = Builder.oper(TlaArithOper.exp.name, NameEx("a") )
    val expBuild = Builder.oper(TlaArithOper.exp.name, NameEx("a"), NameEx("b"))
    val expBuildBad2 = Builder.oper(TlaArithOper.exp.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( expBuildBad1 == NullEx )
    assert( expBuild == OperEx( TlaArithOper.exp, NameEx("a"),NameEx("b") ) )
    assert( expBuildBad2 == NullEx )

    val dotdotBuildBad1 = Builder.oper(TlaArithOper.dotdot.name, NameEx("a") )
    val dotdotBuild = Builder.oper(TlaArithOper.dotdot.name, NameEx("a"), NameEx("b"))
    val dotdotBuildBad2 = Builder.oper(TlaArithOper.dotdot.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( dotdotBuildBad1 == NullEx )
    assert( dotdotBuild == OperEx( TlaArithOper.dotdot, NameEx("a"),NameEx("b") ) )
    assert( dotdotBuildBad2 == NullEx )

    val ltBuildBad1 = Builder.oper(TlaArithOper.lt.name, NameEx("a") )
    val ltBuild = Builder.oper(TlaArithOper.lt.name, NameEx("a"), NameEx("b"))
    val ltBuildBad2 = Builder.oper(TlaArithOper.lt.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( ltBuildBad1 == NullEx )
    assert( ltBuild == OperEx( TlaArithOper.lt, NameEx("a"),NameEx("b") ) )
    assert( ltBuildBad2 == NullEx )

    val gtBuildBad1 = Builder.oper(TlaArithOper.gt.name, NameEx("a") )
    val gtBuild = Builder.oper(TlaArithOper.gt.name, NameEx("a"), NameEx("b"))
    val gtBuildBad2 = Builder.oper(TlaArithOper.gt.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( gtBuildBad1 == NullEx )
    assert( gtBuild == OperEx( TlaArithOper.gt, NameEx("a"),NameEx("b") ) )
    assert( gtBuildBad2 == NullEx )

    val leBuildBad1 = Builder.oper(TlaArithOper.le.name, NameEx("a") )
    val leBuild = Builder.oper(TlaArithOper.le.name, NameEx("a"), NameEx("b"))
    val leBuildBad2 = Builder.oper(TlaArithOper.le.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( leBuildBad1 == NullEx )
    assert( leBuild == OperEx( TlaArithOper.le, NameEx("a"),NameEx("b") ) )
    assert( leBuildBad2 == NullEx )

    val geBuildBad1 = Builder.oper(TlaArithOper.ge.name, NameEx("a") )
    val geBuild = Builder.oper(TlaArithOper.ge.name, NameEx("a"), NameEx("b"))
    val geBuildBad2 = Builder.oper(TlaArithOper.ge.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( geBuildBad1 == NullEx )
    assert( geBuild == OperEx( TlaArithOper.ge, NameEx("a"),NameEx("b") ) )
    assert( geBuildBad2 == NullEx )
  }

  test("Test TlaFiniteSetOper"){

    val cardinalityBuildBad1 = Builder.oper(TlaFiniteSetOper.cardinality.name )
    val cardinalityBuild = Builder.oper(TlaFiniteSetOper.cardinality.name, NameEx("a"))
    val cardinalityBuildBad2 = Builder.oper(TlaFiniteSetOper.cardinality.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( cardinalityBuildBad1 == NullEx )
    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, NameEx("a") ) )
    assert( cardinalityBuildBad2 == NullEx )

    val isFiniteSetBuildBad1 = Builder.oper(TlaFiniteSetOper.isFiniteSet.name )
    val isFiniteSetBuild = Builder.oper(TlaFiniteSetOper.isFiniteSet.name, NameEx("a"))
    val isFiniteSetBuildBad2 = Builder.oper(TlaFiniteSetOper.isFiniteSet.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( isFiniteSetBuildBad1 == NullEx )
    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, NameEx("a") ) )
    assert( isFiniteSetBuildBad2 == NullEx )
    
  }

  test("Test TlaFunOper"){

    val enumBuildEmpty = Builder.oper(TlaFunOper.enum.name)
    val enumBuild = Builder.oper(TlaFunOper.enum.name, NameEx("a"), NameEx("b"))
    val enumBuildBad = Builder.oper(TlaFunOper.enum.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( enumBuildEmpty == NullEx )
    assert( enumBuild == OperEx( TlaFunOper.enum, NameEx("a"), NameEx("b") ) )
    assert( enumBuildBad == NullEx )

    val tupleBuild1 = Builder.oper(TlaFunOper.tuple.name)
    val tupleBuild2 = Builder.oper(TlaFunOper.tuple.name, NameEx("a"), NameEx("b"))

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, NameEx("a"),NameEx("b") ) )

    val appBuildBad1 = Builder.oper(TlaFunOper.app.name, NameEx("a") )
    val appBuild = Builder.oper(TlaFunOper.app.name, NameEx("a"), NameEx("b"))
    val appBuildBad2 = Builder.oper(TlaFunOper.app.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( appBuildBad1 == NullEx )
    assert( appBuild == OperEx( TlaFunOper.app, NameEx("a"),NameEx("b") ) )
    assert( appBuildBad2 == NullEx )

    val domainBuildBad1 = Builder.oper(TlaFunOper.domain.name )
    val domainBuild = Builder.oper(TlaFunOper.domain.name, NameEx("a"))
    val domainBuildBad2 = Builder.oper(TlaFunOper.domain.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( domainBuildBad1 == NullEx )
    assert( domainBuild == OperEx( TlaFunOper.domain, NameEx("a") ) )
    assert( domainBuildBad2 == NullEx )

    val exceptBuildEmpty = Builder.oper(TlaFunOper.except.name)
    val exceptBuildSingle = Builder.oper(TlaFunOper.except.name, NameEx("a"))
    val exceptBuildBad = Builder.oper(TlaFunOper.except.name, NameEx("a"), NameEx("b"))
    val exceptBuild = Builder.oper(TlaFunOper.except.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(exceptBuildEmpty == NullEx )
    assert(exceptBuildSingle == NullEx )
    assert(exceptBuildBad == NullEx )
    assert(exceptBuild == OperEx( TlaFunOper.except, NameEx("a"), NameEx("b"), NameEx("c") ) )

    val funDefBuildEmpty = Builder.oper(TlaFunOper.funDef.name)
    val funDefBuildSingle = Builder.oper(TlaFunOper.funDef.name, NameEx("a"))
    val funDefBuildBad = Builder.oper(TlaFunOper.funDef.name, NameEx("a"), NameEx("b"))
    val funDefBuild = Builder.oper(TlaFunOper.funDef.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(funDefBuildEmpty == NullEx )
    assert(funDefBuildSingle == NullEx )
    assert(funDefBuildBad == NullEx )
    assert(funDefBuild == OperEx( TlaFunOper.funDef, NameEx("a"), NameEx("b"), NameEx("c") ) )

  }

  test("Test TlaSeqOper"){

    assert(true)

//    val appendBuildBad1 = Builder.oper(TlaSeqOper.append.name )
//    val appendBuild = Builder.oper(TlaSeqOper.append.name, NameEx("a"))
//    val appendBuildBad2 = Builder.oper(TlaSeqOper.append.name, NameEx("a"), NameEx("b"), NameEx("c"))
//
//    assert( appendBuildBad1 == NullEx )
//    assert( appendBuild == OperEx( TlaSeqOper.append, NameEx("a") ) )
//    assert( appendBuildBad2 == NullEx )
    
//    TlaSeqOper.concat.name -> TlaSeqOper.concat,
//    TlaSeqOper.head.name   -> TlaSeqOper.head,
//    TlaSeqOper.tail.name   -> TlaSeqOper.tail,
//    TlaSeqOper.len.name    -> TlaSeqOper.len,
  }

  test("Test TlaSetOper"){
    assert(true)
//    TlaSetOper.enumSet.name      -> TlaSetOper.enumSet,
//    TlaSetOper.in.name           -> TlaSetOper.in,
//    TlaSetOper.notin.name        -> TlaSetOper.notin,
//    TlaSetOper.cap.name          -> TlaSetOper.cap,
//    TlaSetOper.cup.name          -> TlaSetOper.cup,
//    TlaSetOper.filter.name       -> TlaSetOper.filter,
//    TlaSetOper.funSet.name       -> TlaSetOper.funSet,
//    TlaSetOper.map.name          -> TlaSetOper.map,
//    TlaSetOper.powerset.name     -> TlaSetOper.powerset,
//    TlaSetOper.recSet.name       -> TlaSetOper.recSet,
//    TlaSetOper.seqSet.name       -> TlaSetOper.seqSet,
//    TlaSetOper.setminus.name     -> TlaSetOper.setminus,
//    TlaSetOper.subseteq.name     -> TlaSetOper.subseteq,
//    TlaSetOper.subsetProper.name -> TlaSetOper.subsetProper,
//    TlaSetOper.supseteq.name     -> TlaSetOper.supseteq,
//    TlaSetOper.supsetProper.name -> TlaSetOper.supsetProper,
//    TlaSetOper.times.name        -> TlaSetOper.times,
//    TlaSetOper.union.name        -> TlaSetOper.union
  }
}

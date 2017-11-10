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
  test("Test direct methods: Names and values"){
    val nameBuild = Builder.name("a")

    assert( nameBuild == NameEx("a") )
  }
  
  test("Test operByNameOrNull: garbage"){
    val garbage = Builder.operByNameOrNull("a string that is obviously not an operator name", NullEx, NameEx("arg2"))
    assert(garbage == NullEx)
  }

  test("Test direct methods: TlaOper"){
    
  }

  test("Test operByNameOrNull: TlaOper"){
    val eqBuildBad1 = Builder.operByNameOrNull(TlaOper.eq.name, NameEx("a"))
    val eqBuild = Builder.operByNameOrNull(TlaOper.eq.name, NameEx("a"), NameEx("b"))
    val eqBuildBad2 = Builder.operByNameOrNull(TlaOper.eq.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert(eqBuildBad1 == NullEx)
    assert(eqBuild == OperEx( TlaOper.eq, NameEx("a"), NameEx("b") ))
    assert(eqBuildBad2 == NullEx)

    val neBuildBad1 = Builder.operByNameOrNull(TlaOper.ne.name, NameEx("a"))
    val neBuild = Builder.operByNameOrNull(TlaOper.ne.name, NameEx("a"), NameEx("b"))
    val neBuildBad2 = Builder.operByNameOrNull(TlaOper.ne.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert(neBuildBad1 == NullEx)
    assert(neBuild == OperEx( TlaOper.ne, NameEx("a"), NameEx("b") ))
    assert(neBuildBad2 == NullEx)

    val cbBuildBad1 = Builder.operByNameOrNull(TlaOper.chooseBounded.name, NameEx("a"), NameEx("b"))
    val cbBuild = Builder.operByNameOrNull(TlaOper.chooseBounded.name, NameEx("a"), NameEx("b"), NameEx("c"))
    val cbBuildBad2 = Builder.operByNameOrNull(TlaOper.chooseBounded.name, NameEx("a"), NameEx("b"), NameEx("c"), NameEx("d"))

    assert(cbBuildBad1 == NullEx)
    assert(cbBuild == OperEx( TlaOper.chooseBounded, NameEx("a"), NameEx("b"), NameEx("c") ))
    assert(cbBuildBad2 == NullEx)

    val cubBuild = Builder.operByNameOrNull(TlaOper.chooseUnbounded.name, NameEx("a"), NameEx("b"))
    val cubBuildBad1 = Builder.operByNameOrNull(TlaOper.chooseUnbounded.name, NameEx("a"), NameEx("b"), NameEx("c"))
    val cubBuildBad2 = Builder.operByNameOrNull(TlaOper.chooseUnbounded.name, NameEx("a"), NameEx("b"), NameEx("c"), NameEx("d"))

    assert(cubBuild == OperEx( TlaOper.chooseUnbounded, NameEx("a"), NameEx("b") ))
    assert(cubBuildBad1 == NullEx)
    assert(cubBuildBad2 == NullEx)
  }

  test("Test operByNameOrNull: TlaActionOper"){
    val primeBuildBad1 = Builder.operByNameOrNull( TlaActionOper.prime.name )
    val primeBuild = Builder.operByNameOrNull( TlaActionOper.prime.name, NameEx("a") )
    val primeBuildBad2 = Builder.operByNameOrNull( TlaActionOper.prime.name, NameEx("a"), NameEx("b") )

    assert(primeBuildBad1 == NullEx)
    assert(primeBuild == OperEx( TlaActionOper.prime, NameEx("a") ))
    assert(primeBuildBad2 == NullEx)

    val stutterBuildBad1 = Builder.operByNameOrNull( TlaActionOper.stutter.name, NameEx("A") )
    val stutterBuild = Builder.operByNameOrNull( TlaActionOper.stutter.name, NameEx("A"), NameEx("e") )
    val stutterBuildBad2 = Builder.operByNameOrNull( TlaActionOper.stutter.name, NameEx("A"), NameEx("e"), NameEx("?") )

    assert(stutterBuildBad1 == NullEx)
    assert(stutterBuild == OperEx( TlaActionOper.stutter, NameEx("A"), NameEx("e") ))
    assert(stutterBuildBad2 == NullEx)

    val nostutterBuildBad1 = Builder.operByNameOrNull( TlaActionOper.nostutter.name, NameEx("A"))
    val nostutterBuild = Builder.operByNameOrNull( TlaActionOper.nostutter.name, NameEx("A"), NameEx("e") )
    val nostutterBuildBad2 = Builder.operByNameOrNull( TlaActionOper.nostutter.name, NameEx("A"), NameEx("e"), NameEx("?") )

    assert(nostutterBuildBad1 == NullEx)
    assert(nostutterBuild == OperEx( TlaActionOper.nostutter, NameEx("A"), NameEx("e") ))
    assert(nostutterBuildBad2 == NullEx)

    val enabledBuildBad1 = Builder.operByNameOrNull( TlaActionOper.enabled.name )
    val enabledBuild = Builder.operByNameOrNull( TlaActionOper.enabled.name, NameEx("A") )
    val enabledBuildBad2 = Builder.operByNameOrNull( TlaActionOper.enabled.name, NameEx("A"), NameEx("b") )

    assert(enabledBuildBad1 == NullEx)
    assert(enabledBuild == OperEx( TlaActionOper.enabled, NameEx("A") ))
    assert(enabledBuildBad2 == NullEx)

    val unchangedBuildBad1 = Builder.operByNameOrNull( TlaActionOper.unchanged.name )
    val unchangedBuild = Builder.operByNameOrNull( TlaActionOper.unchanged.name, NameEx("A") )
    val unchangedBuildBad2 = Builder.operByNameOrNull( TlaActionOper.unchanged.name, NameEx("A"), NameEx("b") )

    assert(unchangedBuildBad1 == NullEx)
    assert(unchangedBuild == OperEx( TlaActionOper.unchanged, NameEx("A") ))
    assert(unchangedBuildBad2 == NullEx)

    val compositionBuildBad1 = Builder.operByNameOrNull( TlaActionOper.composition.name, NameEx("A"))
    val compositionBuild = Builder.operByNameOrNull( TlaActionOper.composition.name, NameEx("A"), NameEx("B") )
    val compositionBuildBad2 = Builder.operByNameOrNull( TlaActionOper.composition.name, NameEx("A"), NameEx("B"), NameEx("?") )

    assert(compositionBuildBad1 == NullEx)
    assert(compositionBuild == OperEx( TlaActionOper.composition, NameEx("A"), NameEx("B") ))
    assert(compositionBuildBad2 == NullEx)

  }

  test("Test operByNameOrNull: TlaControlOper") {
    val caseNoOtherBuildEmpty = Builder.operByNameOrNull(TlaControlOper.caseNoOther.name)
    val caseNoOtherBuild = Builder.operByNameOrNull(TlaControlOper.caseNoOther.name, NameEx("a"), NameEx("b"))
    val caseNoOtherBuildBad = Builder.operByNameOrNull(TlaControlOper.caseNoOther.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(caseNoOtherBuildEmpty == NullEx )
    assert(caseNoOtherBuild == OperEx( TlaControlOper.caseNoOther, NameEx("a"), NameEx("b") ) )
    assert(caseNoOtherBuildBad == NullEx )

    val caseWithOtherBuildEmpty = Builder.operByNameOrNull(TlaControlOper.caseWithOther.name)
    val caseWithOtherBuildSingle = Builder.operByNameOrNull(TlaControlOper.caseWithOther.name, NameEx("a"))
    val caseWithOtherBuildBad = Builder.operByNameOrNull(TlaControlOper.caseWithOther.name, NameEx("a"), NameEx("b"))
    val caseWithOtherBuild = Builder.operByNameOrNull(TlaControlOper.caseWithOther.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(caseWithOtherBuildEmpty == NullEx )
    assert(caseWithOtherBuildSingle == NullEx )
    assert(caseWithOtherBuildBad == NullEx )
    assert(caseWithOtherBuild == OperEx( TlaControlOper.caseWithOther, NameEx("a"), NameEx("b"), NameEx("c") ) )

    val iteBuildBad1 = Builder.operByNameOrNull(TlaControlOper.ifThenElse.name, NameEx("a"), NameEx("b") )
    val iteBuild = Builder.operByNameOrNull(TlaControlOper.ifThenElse.name, NameEx("a"), NameEx("b"), NameEx("c") )
    val iteBuildBad2 = Builder.operByNameOrNull(TlaControlOper.ifThenElse.name, NameEx("a"), NameEx("b"), NameEx("c"), NameEx("d") )

    assert(iteBuildBad1 == NullEx )
    assert(iteBuild == OperEx( TlaControlOper.ifThenElse, NameEx("a"), NameEx("b"), NameEx("c") ) )
    assert(iteBuildBad2 == NullEx )
  }

  test("Test operByNameOrNull: TlaTempOper"){
    val AABuildBad1 = Builder.operByNameOrNull(TlaTempOper.AA.name, NameEx("a") )
    val AABuild = Builder.operByNameOrNull(TlaTempOper.AA.name, NameEx("a"), NameEx("b") )
    val AABuildBad2 = Builder.operByNameOrNull(TlaTempOper.AA.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( AABuildBad1 == NullEx )
    assert( AABuild == OperEx( TlaTempOper.AA, NameEx("a"), NameEx("b") ))
    assert( AABuildBad2 == NullEx )

    val EEBuildBad1 = Builder.operByNameOrNull(TlaTempOper.EE.name, NameEx("a") )
    val EEBuild = Builder.operByNameOrNull(TlaTempOper.EE.name, NameEx("a"), NameEx("b") )
    val EEBuildBad2 = Builder.operByNameOrNull(TlaTempOper.EE.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( EEBuildBad1 == NullEx )
    assert( EEBuild == OperEx( TlaTempOper.EE, NameEx("a"), NameEx("b") ))
    assert( EEBuildBad2 == NullEx )

    val boxBuildBad1 = Builder.operByNameOrNull(TlaTempOper.box.name )
    val boxBuild = Builder.operByNameOrNull(TlaTempOper.box.name, NameEx("a"))
    val boxBuildBad2 = Builder.operByNameOrNull(TlaTempOper.box.name, NameEx("a"), NameEx("b"))

    assert( boxBuildBad1 == NullEx )
    assert( boxBuild == OperEx( TlaTempOper.box, NameEx("a") ))
    assert( boxBuildBad2 == NullEx )

    val diamondBuildBad1 = Builder.operByNameOrNull(TlaTempOper.diamond.name )
    val diamondBuild = Builder.operByNameOrNull(TlaTempOper.diamond.name, NameEx("a"))
    val diamondBuildBad2 = Builder.operByNameOrNull(TlaTempOper.diamond.name, NameEx("a"), NameEx("b"))

    assert( diamondBuildBad1 == NullEx )
    assert( diamondBuild == OperEx( TlaTempOper.diamond, NameEx("a") ))
    assert( diamondBuildBad2 == NullEx )

    val leadsToBuildBad1 = Builder.operByNameOrNull(TlaTempOper.leadsTo.name, NameEx("a") )
    val leadsToBuild = Builder.operByNameOrNull(TlaTempOper.leadsTo.name, NameEx("a"), NameEx("b") )
    val leadsToBuildBad2 = Builder.operByNameOrNull(TlaTempOper.leadsTo.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( leadsToBuildBad1 == NullEx )
    assert( leadsToBuild == OperEx( TlaTempOper.leadsTo, NameEx("a"), NameEx("b") ))
    assert( leadsToBuildBad2 == NullEx )

    val guaranteesBuildBad1 = Builder.operByNameOrNull(TlaTempOper.guarantees.name, NameEx("a") )
    val guaranteesBuild = Builder.operByNameOrNull(TlaTempOper.guarantees.name, NameEx("a"), NameEx("b") )
    val guaranteesBuildBad2 = Builder.operByNameOrNull(TlaTempOper.guarantees.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( guaranteesBuildBad1 == NullEx )
    assert( guaranteesBuild == OperEx( TlaTempOper.guarantees, NameEx("a"), NameEx("b") ))
    assert( guaranteesBuildBad2 == NullEx )

    val strongFairnessBuildBad1 = Builder.operByNameOrNull(TlaTempOper.strongFairness.name, NameEx("a") )
    val strongFairnessBuild = Builder.operByNameOrNull(TlaTempOper.strongFairness.name, NameEx("a"), NameEx("b") )
    val strongFairnessBuildBad2 = Builder.operByNameOrNull(TlaTempOper.strongFairness.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( strongFairnessBuildBad1 == NullEx )
    assert( strongFairnessBuild == OperEx( TlaTempOper.strongFairness, NameEx("a"), NameEx("b") ))
    assert( strongFairnessBuildBad2 == NullEx )

    val weakFairnessBuildBad1 = Builder.operByNameOrNull(TlaTempOper.weakFairness.name, NameEx("a") )
    val weakFairnessBuild = Builder.operByNameOrNull(TlaTempOper.weakFairness.name, NameEx("a"), NameEx("b") )
    val weakFairnessBuildBad2 = Builder.operByNameOrNull(TlaTempOper.weakFairness.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( weakFairnessBuildBad1 == NullEx )
    assert( weakFairnessBuild == OperEx( TlaTempOper.weakFairness, NameEx("a"), NameEx("b") ))
    assert( weakFairnessBuildBad2 == NullEx )
  }

  test("Test operByNameOrNull: TlaArithOper"){
    val sumBuild1 = Builder.operByNameOrNull(TlaArithOper.sum.name)
    val sumBuild2 = Builder.operByNameOrNull(TlaArithOper.sum.name, NameEx("a"), NameEx("b"))

    assert( sumBuild1 == OperEx( TlaArithOper.sum ) )
    assert( sumBuild2 == OperEx( TlaArithOper.sum, NameEx("a"),NameEx("b") ) )

    val plusBuildBad1 = Builder.operByNameOrNull(TlaArithOper.plus.name, NameEx("a") )
    val plusBuild = Builder.operByNameOrNull(TlaArithOper.plus.name, NameEx("a"), NameEx("b"))
    val plusBuildBad2 = Builder.operByNameOrNull(TlaArithOper.plus.name, NameEx("a"), NameEx("b"), NameEx("c"))
    
    assert( plusBuildBad1 == NullEx )
    assert( plusBuild == OperEx( TlaArithOper.plus, NameEx("a"),NameEx("b") ) )
    assert( plusBuildBad2 == NullEx )

    val minusBuildBad1 = Builder.operByNameOrNull(TlaArithOper.minus.name, NameEx("a") )
    val minusBuild = Builder.operByNameOrNull(TlaArithOper.minus.name, NameEx("a"), NameEx("b"))
    val minusBuildBad2 = Builder.operByNameOrNull(TlaArithOper.minus.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( minusBuildBad1 == NullEx )
    assert( minusBuild == OperEx( TlaArithOper.minus, NameEx("a"),NameEx("b") ) )
    assert( minusBuildBad2 == NullEx )

    val uminusBuildBad1 = Builder.operByNameOrNull(TlaArithOper.uminus.name )
    val uminusBuild = Builder.operByNameOrNull(TlaArithOper.uminus.name, NameEx("a"))
    val uminusBuildBad2 = Builder.operByNameOrNull(TlaArithOper.uminus.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( uminusBuildBad1 == NullEx )
    assert( uminusBuild == OperEx( TlaArithOper.uminus, NameEx("a") ) )
    assert( uminusBuildBad2 == NullEx )

    val prodBuild1 = Builder.operByNameOrNull(TlaArithOper.prod.name)
    val prodBuild2 = Builder.operByNameOrNull(TlaArithOper.prod.name, NameEx("a"), NameEx("b"))

    assert( prodBuild1 == OperEx( TlaArithOper.prod ) )
    assert( prodBuild2 == OperEx( TlaArithOper.prod, NameEx("a"),NameEx("b") ) )

    val multBuildBad1 = Builder.operByNameOrNull(TlaArithOper.mult.name, NameEx("a") )
    val multBuild = Builder.operByNameOrNull(TlaArithOper.mult.name, NameEx("a"), NameEx("b"))
    val multBuildBad2 = Builder.operByNameOrNull(TlaArithOper.mult.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( multBuildBad1 == NullEx )
    assert( multBuild == OperEx( TlaArithOper.mult, NameEx("a"),NameEx("b") ) )
    assert( multBuildBad2 == NullEx )

    val divBuildBad1 = Builder.operByNameOrNull(TlaArithOper.div.name, NameEx("a") )
    val divBuild = Builder.operByNameOrNull(TlaArithOper.div.name, NameEx("a"), NameEx("b"))
    val divBuildBad2 = Builder.operByNameOrNull(TlaArithOper.div.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( divBuildBad1 == NullEx )
    assert( divBuild == OperEx( TlaArithOper.div, NameEx("a"),NameEx("b") ) )
    assert( divBuildBad2 == NullEx )

    val modBuildBad1 = Builder.operByNameOrNull(TlaArithOper.mod.name, NameEx("a") )
    val modBuild = Builder.operByNameOrNull(TlaArithOper.mod.name, NameEx("a"), NameEx("b"))
    val modBuildBad2 = Builder.operByNameOrNull(TlaArithOper.mod.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( modBuildBad1 == NullEx )
    assert( modBuild == OperEx( TlaArithOper.mod, NameEx("a"),NameEx("b") ) )
    assert( modBuildBad2 == NullEx )

    val realDivBuildBad1 = Builder.operByNameOrNull(TlaArithOper.realDiv.name, NameEx("a") )
    val realDivBuild = Builder.operByNameOrNull(TlaArithOper.realDiv.name, NameEx("a"), NameEx("b"))
    val realDivBuildBad2 = Builder.operByNameOrNull(TlaArithOper.realDiv.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( realDivBuildBad1 == NullEx )
    assert( realDivBuild == OperEx( TlaArithOper.realDiv, NameEx("a"),NameEx("b") ) )
    assert( realDivBuildBad2 == NullEx )

    val expBuildBad1 = Builder.operByNameOrNull(TlaArithOper.exp.name, NameEx("a") )
    val expBuild = Builder.operByNameOrNull(TlaArithOper.exp.name, NameEx("a"), NameEx("b"))
    val expBuildBad2 = Builder.operByNameOrNull(TlaArithOper.exp.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( expBuildBad1 == NullEx )
    assert( expBuild == OperEx( TlaArithOper.exp, NameEx("a"),NameEx("b") ) )
    assert( expBuildBad2 == NullEx )

    val dotdotBuildBad1 = Builder.operByNameOrNull(TlaArithOper.dotdot.name, NameEx("a") )
    val dotdotBuild = Builder.operByNameOrNull(TlaArithOper.dotdot.name, NameEx("a"), NameEx("b"))
    val dotdotBuildBad2 = Builder.operByNameOrNull(TlaArithOper.dotdot.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( dotdotBuildBad1 == NullEx )
    assert( dotdotBuild == OperEx( TlaArithOper.dotdot, NameEx("a"),NameEx("b") ) )
    assert( dotdotBuildBad2 == NullEx )

    val ltBuildBad1 = Builder.operByNameOrNull(TlaArithOper.lt.name, NameEx("a") )
    val ltBuild = Builder.operByNameOrNull(TlaArithOper.lt.name, NameEx("a"), NameEx("b"))
    val ltBuildBad2 = Builder.operByNameOrNull(TlaArithOper.lt.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( ltBuildBad1 == NullEx )
    assert( ltBuild == OperEx( TlaArithOper.lt, NameEx("a"),NameEx("b") ) )
    assert( ltBuildBad2 == NullEx )

    val gtBuildBad1 = Builder.operByNameOrNull(TlaArithOper.gt.name, NameEx("a") )
    val gtBuild = Builder.operByNameOrNull(TlaArithOper.gt.name, NameEx("a"), NameEx("b"))
    val gtBuildBad2 = Builder.operByNameOrNull(TlaArithOper.gt.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( gtBuildBad1 == NullEx )
    assert( gtBuild == OperEx( TlaArithOper.gt, NameEx("a"),NameEx("b") ) )
    assert( gtBuildBad2 == NullEx )

    val leBuildBad1 = Builder.operByNameOrNull(TlaArithOper.le.name, NameEx("a") )
    val leBuild = Builder.operByNameOrNull(TlaArithOper.le.name, NameEx("a"), NameEx("b"))
    val leBuildBad2 = Builder.operByNameOrNull(TlaArithOper.le.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( leBuildBad1 == NullEx )
    assert( leBuild == OperEx( TlaArithOper.le, NameEx("a"),NameEx("b") ) )
    assert( leBuildBad2 == NullEx )

    val geBuildBad1 = Builder.operByNameOrNull(TlaArithOper.ge.name, NameEx("a") )
    val geBuild = Builder.operByNameOrNull(TlaArithOper.ge.name, NameEx("a"), NameEx("b"))
    val geBuildBad2 = Builder.operByNameOrNull(TlaArithOper.ge.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( geBuildBad1 == NullEx )
    assert( geBuild == OperEx( TlaArithOper.ge, NameEx("a"),NameEx("b") ) )
    assert( geBuildBad2 == NullEx )
  }

  test("Test operByNameOrNull: TlaFiniteSetOper"){
    val cardinalityBuildBad1 = Builder.operByNameOrNull(TlaFiniteSetOper.cardinality.name )
    val cardinalityBuild = Builder.operByNameOrNull(TlaFiniteSetOper.cardinality.name, NameEx("a"))
    val cardinalityBuildBad2 = Builder.operByNameOrNull(TlaFiniteSetOper.cardinality.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( cardinalityBuildBad1 == NullEx )
    assert( cardinalityBuild == OperEx( TlaFiniteSetOper.cardinality, NameEx("a") ) )
    assert( cardinalityBuildBad2 == NullEx )

    val isFiniteSetBuildBad1 = Builder.operByNameOrNull(TlaFiniteSetOper.isFiniteSet.name )
    val isFiniteSetBuild = Builder.operByNameOrNull(TlaFiniteSetOper.isFiniteSet.name, NameEx("a"))
    val isFiniteSetBuildBad2 = Builder.operByNameOrNull(TlaFiniteSetOper.isFiniteSet.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( isFiniteSetBuildBad1 == NullEx )
    assert( isFiniteSetBuild == OperEx( TlaFiniteSetOper.isFiniteSet, NameEx("a") ) )
    assert( isFiniteSetBuildBad2 == NullEx )
    
  }

  test("Test operByNameOrNull: TlaFunOper"){
    val enumBuildEmpty = Builder.operByNameOrNull(TlaFunOper.enum.name)
    val enumBuild = Builder.operByNameOrNull(TlaFunOper.enum.name, NameEx("a"), NameEx("b"))
    val enumBuildBad = Builder.operByNameOrNull(TlaFunOper.enum.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert( enumBuildEmpty == NullEx )
    assert( enumBuild == OperEx( TlaFunOper.enum, NameEx("a"), NameEx("b") ) )
    assert( enumBuildBad == NullEx )

    val tupleBuild1 = Builder.operByNameOrNull(TlaFunOper.tuple.name)
    val tupleBuild2 = Builder.operByNameOrNull(TlaFunOper.tuple.name, NameEx("a"), NameEx("b"))

    assert( tupleBuild1 == OperEx( TlaFunOper.tuple ) )
    assert( tupleBuild2 == OperEx( TlaFunOper.tuple, NameEx("a"),NameEx("b") ) )

    val appBuildBad1 = Builder.operByNameOrNull(TlaFunOper.app.name, NameEx("a") )
    val appBuild = Builder.operByNameOrNull(TlaFunOper.app.name, NameEx("a"), NameEx("b"))
    val appBuildBad2 = Builder.operByNameOrNull(TlaFunOper.app.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( appBuildBad1 == NullEx )
    assert( appBuild == OperEx( TlaFunOper.app, NameEx("a"),NameEx("b") ) )
    assert( appBuildBad2 == NullEx )

    val domainBuildBad1 = Builder.operByNameOrNull(TlaFunOper.domain.name )
    val domainBuild = Builder.operByNameOrNull(TlaFunOper.domain.name, NameEx("a"))
    val domainBuildBad2 = Builder.operByNameOrNull(TlaFunOper.domain.name, NameEx("a"), NameEx("b"), NameEx("c"))

    assert( domainBuildBad1 == NullEx )
    assert( domainBuild == OperEx( TlaFunOper.domain, NameEx("a") ) )
    assert( domainBuildBad2 == NullEx )

    val exceptBuildEmpty = Builder.operByNameOrNull(TlaFunOper.except.name)
    val exceptBuildSingle = Builder.operByNameOrNull(TlaFunOper.except.name, NameEx("a"))
    val exceptBuildBad = Builder.operByNameOrNull(TlaFunOper.except.name, NameEx("a"), NameEx("b"))
    val exceptBuild = Builder.operByNameOrNull(TlaFunOper.except.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(exceptBuildEmpty == NullEx )
    assert(exceptBuildSingle == NullEx )
    assert(exceptBuildBad == NullEx )
    assert(exceptBuild == OperEx( TlaFunOper.except, NameEx("a"), NameEx("b"), NameEx("c") ) )

    val funDefBuildEmpty = Builder.operByNameOrNull(TlaFunOper.funDef.name)
    val funDefBuildSingle = Builder.operByNameOrNull(TlaFunOper.funDef.name, NameEx("a"))
    val funDefBuildBad = Builder.operByNameOrNull(TlaFunOper.funDef.name, NameEx("a"), NameEx("b"))
    val funDefBuild = Builder.operByNameOrNull(TlaFunOper.funDef.name, NameEx("a"), NameEx("b"), NameEx("c") )

    assert(funDefBuildEmpty == NullEx )
    assert(funDefBuildSingle == NullEx )
    assert(funDefBuildBad == NullEx )
    assert(funDefBuild == OperEx( TlaFunOper.funDef, NameEx("a"), NameEx("b"), NameEx("c") ) )
  }

  test("Test operByNameOrNull: TlaSeqOper"){

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

  test("Test operByNameOrNull: TlaSetOper"){
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

  test("Test operByNameOrNull: TlaBoolOper "){
    assert(true)
//    TlaBoolOper.and.name -> TlaBoolOper.and,
//    TlaBoolOper.or.name -> TlaBoolOper.or,
//    TlaBoolOper.not.name -> TlaBoolOper.not,
//    TlaBoolOper.implies.name -> TlaBoolOper.implies,
//    TlaBoolOper.equiv.name -> TlaBoolOper.equiv,
//    TlaBoolOper.forall.name -> TlaBoolOper.forall,
//    TlaBoolOper.exists.name -> TlaBoolOper.exists,
//    TlaBoolOper.forallUnbounded.name -> TlaBoolOper.forallUnbounded,
//    TlaBoolOper.existsUnbounded.name -> TlaBoolOper.existsUnbounded,
  }
}

package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.types.Names.{dtName, intTName, tupTName}
import at.forsyte.apalache.tla.types.smt.TypeRecovery
import com.microsoft.z3._
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestRecovery extends FunSuite with TestingPredefs with BeforeAndAfter {
  val limits = SpecLimits( 3, Set("a","b" ) )

  var ctx      = new Context
  var tvg      = new TypeVarGenerator
  var recovery = new TypeRecovery( tvg, limits, None )

  before {
    ctx = new Context
    tvg = new TypeVarGenerator
    var recovery = new TypeRecovery( tvg, limits, None )
  }

  test( "Test tupT" ) {
    // TODO
  }
}

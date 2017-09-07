package at.forsyte.apalache.tla.testing

import at.forsyte.apalache.tla.lir.plugins.types._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Tests for the TLA+ types that we can construct.
  */
@RunWith(classOf[JUnitRunner])
class TestTypes extends FunSuite {
  test("Check subtype relations") {
    val setType1 = FinSet( TInt(), SetCell() ) // empty
    val setType2 = FinSet( Fun( setType1, TBool()), SetCell( SymbCell( "f" )) )

    assert( setType1 <= setType2 && !(setType2 <= setType1) )

    val setType3 = PowSet( setType1 )
    val setType4 = PowSet( setType2 )

    print( setType4 )
  }

}

package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.TestingPredefs
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestStrIdConverter extends FunSuite with TestingPredefs with BeforeAndAfter {
  var sic = new StrIdConverter

  before {
    sic = new StrIdConverter
  }

  test( "Add" ) {
    assert( sic.allStrings.isEmpty )
    val s = "s"
    sic.add( s )
    val all = sic.allStrings
    assert( all.exists {
      _ == s
    } )
    sic.add( s )
    assert( all == sic.allStrings )
  }

  test( "Accessors" ) {
    val s = "s"
    sic.add( s )
    assert( sic.stringToId( "s" ) contains 0 )
    assert( sic.idToString( 0 ) contains s )
    assert( sic.idToString( 42 ).isEmpty )
    assert( sic.stringToId( "x" ).isEmpty )
  }

  test( "Collections" ) {
    sic.add( "a" )
    sic.add( "b" )
    sic.add( "c" )

    assert( sic.allStrings.size == sic.allStringIds.size )
  }
}

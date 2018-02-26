package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.plugins.{Identifier, UniqueDB}

import at.forsyte.apalache.tla.lir.{Builder => bd}

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestWarningDetector extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/WarningDetector/"

  test( "NoWarning" ){
    val next = n_x

    val ret = WarningDetector( next )

    assert( ret.isTrivial && ret.toString == "No warnings to report.")

  }

  test( "test" ){
    val file = "test1.tla"

    UniqueDB.clear()
    val converter = new Transformer()

    val decls = declarationsFromFile(testFolderPath + file)
    decls.foreach( Identifier.identify )
//    converter.extract( decls:_* )

    val nextBody = findBodyOf( "Next", decls:_* )

    println( nextBody )

    assert( ! nextBody.isNull )
    assert( nextBody.ID.valid )

    val ret = WarningDetector( nextBody )

    assert( !ret.isTrivial )
    println( ret.message )
  }

}

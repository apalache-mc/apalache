package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.plugins.{Identifier, UniqueDB}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestWarningDetector extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/WarningDetector/"

  test( "test" ){
    val file = "test1.tla"

    UniqueDB.clear()
    Converter.clear()

    val decls = declarationsFromFile(testFolderPath + file)
    decls.foreach( Identifier.identify )
    Converter.extract( decls:_* )

    val nextBody = findBodyOf( "Next", decls:_* )

    println( nextBody )

    assert( ! nextBody.isNull )
    assert( nextBody.ID.valid )

    val ret = WarningDetector( nextBody )

    assert( !ret.isTrivial )
    println( ret.message )
  }
}

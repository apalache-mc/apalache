package at.forsyte.apalache.tla.types

import java.io.File
import java.nio.file.Paths

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin, WriteablePassOptions}
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.types.passes.TypeAnnotationPassImpl
import org.junit.runner.RunWith
import org.scalatest.exceptions.TestFailedException
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

@RunWith( classOf[JUnitRunner] )
class TestTypeAnnotationPass extends FunSuite with TestingPredefs with BeforeAndAfter {
  val testFolderPath = "src/test/resources/"

  val dummyPass : Pass with TlaModuleMixin = new Pass with TlaModuleMixin {
    override def name = ""

    override def execute( ) = true

    override def next( ) : Option[Pass] = None
  }

  def testFromFile( fileName : String ) : Unit = {

    val (rootName, modules) =
      new SanyImporter( new SourceStore ).loadFromFile( new File( testFolderPath + fileName ) )

    val module = modules( rootName )

    val options = new WriteablePassOptions
    val outDir = new File( s"${testFolderPath}out/" )
    if (!outDir.exists()) {
      outDir.mkdir()
    }
    options.set( "io.outdir", Paths.get( outDir.getAbsolutePath ) )

    val pass = new TypeAnnotationPassImpl(
      options,
      dummyPass
    )

    pass.setModule( module )
    assert( pass.execute() )
  }

  test( "Test: test1.tla" ) {
    testFromFile( "test1.tla" )
  }

  test( "Test: test2.tla" ) {
    testFromFile( "test2.tla" )
  }

  test( "Test: test3.tla" ) {
    testFromFile( "test3.tla" )
  }

  test( "Test: test4.tla" ) {
    testFromFile( "test4.tla" )
  }

  test( "Test: test5.tla" ) {
    assertThrows[TestFailedException] {
      testFromFile( "test5.tla" )
    }
  }

  test( "Test: test6.tla" ) {
    testFromFile( "test6.tla" )
  }

  test( "Test: Paxos" ) {
    testFromFile( "realSpecs/Paxos.tla" )
  }

  test( "Test: Blockchain" ) {
    testFromFile( "realSpecs/BlockchainP1.tla" )
  }

//  test( "Test: Lightclient" ) {
//    testFromFile( "realSpecs/LightclientV1P1.tla" )
//  }

}

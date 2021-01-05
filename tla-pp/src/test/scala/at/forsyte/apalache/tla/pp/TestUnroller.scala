package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

import scala.math.BigInt


@RunWith( classOf[JUnitRunner] )
class TestUnroller extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  val noTracker = TrackerWithListeners()
  private var unroller = new Unroller( new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker) )

  override def beforeEach( ) : Unit = {
    unroller = new Unroller( new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker) )
  }

  def exAsDecl(pa: (String, TlaEx)): TlaOperDecl = TlaOperDecl( pa._1, List.empty, pa._2 )

  test("No-op"){
    val decls = Seq[(String, TlaEx)](
      ("A", "1"),
      ("B", 0),
      ("C", tla.and( n_x, n_P )),
      ("D", tla.letIn( n_T, tla.declOp( "T", "p", "p" ) ) )
    ) map exAsDecl

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    assert( module.declarations == unrolled.declarations )
  }

  test("0 step: ParamNormalForm"){
    val name = "A"

    // A(p) == A(p)
    val recDecl = tla.declOp( name, tla.appOp( n_A, n_p ), "p")
    recDecl.isRecursive = true

    val defaultVal : BigInt = 42

    val decls = recDecl +: (Seq[(String,TlaEx)](
      (Unroller.UNROLL_TIMES_PREFIX + name, 0),
      (Unroller.UNROLL_DEFAULT_PREFIX + name, defaultVal.intValue)
    ) map exAsDecl )

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    val newAOpt = unrolled.operDeclarations.find( _.name == name )

    val assertCond = newAOpt.exists{
      case d@TlaOperDecl( _, _, body ) => !d.isRecursive &&
        ( body match {
          case LetInEx( ValEx( TlaInt( `defaultVal` ) ), TlaOperDecl( _, Nil, NameEx( "p" ) ) ) =>
            true
          case _ => false
        } )
    }

    assert( assertCond )
  }

  test("1 step: Nontrivial inlining") {
    val name = "A"

    // A(p) == A(p)
    val recDecl = tla.declOp( name, tla.appOp( n_A, n_p ), "p" )
    recDecl.isRecursive = true

    val defaultVal : BigInt = 42

    val decls = recDecl +: ( Seq[(String, TlaEx)](
      (Unroller.UNROLL_TIMES_PREFIX + name, 1),
      (Unroller.UNROLL_DEFAULT_PREFIX + name, defaultVal.intValue)
    ) map exAsDecl )

    val module = new TlaModule( "M", decls )

    val unrolled = unroller( module )

    val newAOpt = unrolled.operDeclarations.find( _.name == name )

    val assertCond = newAOpt.exists {
      case d@TlaOperDecl( _, _, body ) => !d.isRecursive &&
        ( body match {
          case LetInEx( paramNormalBody, TlaOperDecl( uniqueName, Nil, NameEx( "p" ) ) ) =>
            paramNormalBody match {
              case LetInEx(
              ValEx( TlaInt( `defaultVal` ) ),
              TlaOperDecl( _, Nil, OperEx( TlaOper.apply, NameEx( `uniqueName` ) ) ) ) =>
                true
              case _ => false
            }
          case _ => false
        } )
    }

    assert( assertCond )

  }

  test( "Recursive LET-IN inside non-recursive operator" ){
    val letInOpName = "A"

    // A(p) == A(p)
    val recDecl = tla.declOp( letInOpName, tla.appOp( n_A, n_p ), "p" )
    recDecl.isRecursive = true

    val appEx = tla.appDecl( recDecl, 99 )
    // X == LET A(p) == A(p) IN A(99)
    val nonRecDecl = tla.declOp( "X", tla.letIn( appEx, recDecl ) )

    val defaultVal : BigInt = 42

    val decls = nonRecDecl +: ( Seq[(String, TlaEx)](
      (Unroller.UNROLL_TIMES_PREFIX + letInOpName, 1),
      (Unroller.UNROLL_DEFAULT_PREFIX + letInOpName, defaultVal.intValue)
    ) map exAsDecl )

    val module = new TlaModule( "M", decls )

    val unrolled = unroller( module )

    val newXOpt = unrolled.operDeclarations.find( _.name == "X" )

    // The test is: Does an embedded LET-IN get unrolled in the same way as a top-level declaration

    // reset Renaming
    unroller = new Unroller( new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker) )

    val altDecls = recDecl +: ( Seq[(String, TlaEx)](
      (Unroller.UNROLL_TIMES_PREFIX + letInOpName, 1),
      (Unroller.UNROLL_DEFAULT_PREFIX + letInOpName, defaultVal.intValue)
    ) map exAsDecl )

    val altModule = new TlaModule("N", altDecls)
    val altUnrolled = unroller( altModule )

    val aUnrolledOpt =  altUnrolled.operDeclarations.find( _.name == letInOpName )

    assert( aUnrolledOpt.nonEmpty )

    val aUnrolledBody = aUnrolledOpt.get.body

    val assertCond = newXOpt.exists {
      case d@TlaOperDecl( _, _, body ) => body match {
        case LetInEx( `appEx`, TlaOperDecl( `letInOpName`, List(SimpleFormalParam("p")), `aUnrolledBody` ) ) =>
            true
          case _ => false
        }
    }

    assert( assertCond )

  }

}

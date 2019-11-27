package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.smt.SmtTools.And
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.types.smt.{SmtVarGenerator, Z3TypeSolver}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestZ3TypeSolver extends FunSuite with TestingPredefs with BeforeAndAfter {

  import at.forsyte.apalache.tla.lir.{Builder => tla}

  var smtVarGen = new SmtVarGenerator

  var globNC : NameContext = Map(
    "x" -> smtVarGen.getFresh,
    "y" -> smtVarGen.getFresh
  )

  val globBM : BodyMap = Map.empty

  var udtg   = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )
  var solver = new Z3TypeSolver( useSoftConstraints = true )

  before {
    smtVarGen = new SmtVarGenerator
    globNC = Map(
      "x" -> smtVarGen.getFresh,
      "y" -> smtVarGen.getFresh
    )
    udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )
    solver = new Z3TypeSolver( useSoftConstraints = true )
  }


  test( "Simple operator" ) {

    val par1 = SimpleFormalParam( "p" )
    val par2 = OperFormalParam( "O", 2 )

    val plusEx = tla.plus( n_x, n_y )

    val body = tla.appOp( tla.name( par2.name ),
      plusEx,
      n_p
    )

    /**
      * X(p, O(_,_)) == O( x + y, p )
      */
    val operX = TlaOperDecl( "X", List( par1, par2 ), body )

    val e = smtVarGen.getFresh
    val ts@List( t1, t2 ) = smtVarGen.getNFresh( operX.formalParams.length )

    val templ = udtg.makeTemplate( operX.formalParams, operX.body )
    val templApp = templ( e +: ts ).asInstanceOf[And]

    val ret = solver.solve( smtVarGen.allVars, templApp )
    assert( ret.nonEmpty )
    val solution = ret.get

    val ctx = udtg.getCtx
    val varOfPlusEx = ctx( List.empty )( plusEx.ID )

    assert( varOfPlusEx match {
      case i : SmtTypeVariable =>
        solution( i ) == IntT
      case _ => false
    } )
  }

  test( "H.O. operators" ) {
    // A(p) == p
    val declA = tla.declOp( "A", n_p, "p" )
    // B(O(_)) == O(1)
    val declB = tla.declOp( "B", tla.appOp( tla.name( "O" ), tla.int( 1 ) ), ("O", 1) )
    // C == B(A)
    val declC = tla.declOp( "C", tla.appOp( tla.name( declB.name ), tla.name( declA.name ) ) )

    val decls = List( declA, declB, declC )
    val bodyMap = BodyMapFactory.makeFromDecls( decls )
    udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, bodyMap )

    val e = smtVarGen.getFresh

    val templ = udtg.makeTemplate( List.empty, declC.body )
    val templApp = templ( e +: Nil ).asInstanceOf[And]

    val ret = solver.solve( smtVarGen.allVars, templApp )

    assert( ret.nonEmpty )
  }

  test( "Misc. Tuples" ) {
    val ex = tla.and(
      tla.eql( n_x, tla.tuple( tla.int( 1 ), tla.str( "a" ) ) ),
      tla.eql( n_y, tla.tuple( tla.str( "b" ), tla.int( 2 ), tla.str( "c" ) ) )
    )

    val e = smtVarGen.getFresh

    val templ = udtg.makeTemplate( List.empty, ex )
    val templApp = templ( e +: Nil ).asInstanceOf[And]

    val ret = solver.solve( smtVarGen.allVars, templApp )

    assert( ret.nonEmpty )
  }

}

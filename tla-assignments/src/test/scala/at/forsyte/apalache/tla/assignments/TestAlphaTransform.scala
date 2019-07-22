package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.process.DeclarationModifiers
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory, SourceStoreImpl}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard.ExplicitLetIn
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestAlphaTransform extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/assignmentSolver/"

  def specFromFile(p_file : String, p_next : String = "Next") : TlaEx = {
    val declsRaw = declarationsFromFile(testFolderPath + p_file)

    val declsRenamed = declsRaw map {
        DeclarationModifiers.uniqueVarRename( _ )
      }

    val tracker = TrackerWithListeners( new SourceStoreImpl )

    /** Make all LET-IN calls explicit, to move towards alpha-TLA+ */
    val decls = declsRenamed.map(
      {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params, ExplicitLetIn( tracker )( body ) )
        case e@_ => e
      }
    )

    /** Extract transition relation */
    val nextBody = findBodyOf( p_next, decls : _* )

    /** If extraction failed, throw */
    //    assert( !nextBody.isNull )
    if ( nextBody == NullEx )
      throw new AssignmentException(
        "%s not found or not an operator".format( p_next )
      )

    val transformer = StandardTransformer( BodyMapFactory.newMap, tracker )

    /** Preprocess body (inline operators, replace UNCHANGED, turn equality to set membership, etc.) */
    val cleaned = transformer( nextBody ) match {
      case NullEx => None
      case e => Some( e )
    }

    /** Sanity check */
    assert( cleaned.isDefined )

    cleaned.get
  }

  test( "Star abstraction" ) {

    val ex1 = trueEx
    val ex2 : TlaEx = 5
    val ex3 : TlaEx = x_in_S
    val ex4 : TlaEx = tla.choose( n_x, n_S, n_p )
    val ex5 : TlaEx = tla.caseOther( n_c, n_p, n_a, n_q, n_b )
    val ex6 : TlaEx = tla.card( n_S )

    val exs = List( ex1, ex2, ex3, ex4, ex5, ex6 )

    assert( exs forall { ex =>
      AlphaTransform( ex ) == Star( ex )
    } )

  }

  test( "No abstraction" ) {

    val ex1 = falseEx
    val ex2 : TlaEx = tla.primeInSingleton( n_x, 1 )
    val ex3 : TlaEx = tla.ite( n_p, n_a, n_b )
    val ex4 : TlaEx = tla.or( ex1, ex2, ex3 )
    val ex5 : TlaEx = tla.and( ex1, ex2, ex3 )

    val exs = List( ex1, ex2, ex3, ex4, ex5 )

    assert( exs forall { ex =>
      !AlphaTransform( ex ).isInstanceOf[Star]
    } )

  }


  def correctRecursiveApplication( exs: Traversable[TlaEx] ): Boolean = {
    val trs = ( exs map { ex => ex -> AlphaTransform( ex ) } ).toMap
    def argMatch( exargs: Traversable[TlaEx], args: Traversable[AlphaEx] ): Boolean =
      ( exargs map { arg => trs.getOrElse(arg, AlphaTransform(arg)) } ) == args

    trs forall { case (ex@OperEx( _, _* ), tr) => tr match {
      case AndOr( OperEx( _, exargs@_* ), args@_* ) => argMatch( exargs, args )
      case ITE( OperEx( _, exargs@_* ), i, t, e ) => argMatch( exargs, Seq(i,t,e) )
      case Exists( OperEx( _, exargs@_* ), x, s, b ) => argMatch( exargs, Seq(x,s,b) )
      case AsgnEx( OperEx( _, exargs@_* ), v, r ) => argMatch( exargs.tail, Seq(r)) // skip variable
      case Star( e ) => e == ex
      case _ => false
    }
    case (ex, tr) => tr == trs(ex)
    }
  }

  test( "And/Or nesting" ) {

    val ex1 = trueEx
    val ex2 = falseEx
    val ex3 = tla.and( ex1, ex2 )
    val ex4 = tla.or( ex1, ex2 )

    val ex5 = tla.and( ex4, ex3 )
    val ex6 = tla.or( ex5, ex4, ex3, ex2, ex1 )

    val exs : List[TlaEx] = List( ex1, ex2, ex3, ex4, ex5, ex6 )

    assert( correctRecursiveApplication( exs ) )
  }

  test( "QuantAlt" ) {
    val ex1 = tla.forall( n_x, n_S, tla.exists( n_y, n_T, tla.eql( 1, 2 ) ) )
    val ex2 = tla.exists( n_x, n_S, tla.forall( n_y, n_T, tla.eql( 1, 2 ) ) )

    assert( correctRecursiveApplication( Seq(ex1, ex2) ) )
  }

  test( "ITE nesting" ) {
    val ex1 = tla.and( trueEx, falseEx, trueEx, trueEx, falseEx)
    val ex2 = tla.exists( n_x, n_S, tla.primeInSingleton( n_t, n_x ) )
    val ex3 = tla.ite( n_p, ex1, ex2 )

    assert( correctRecursiveApplication( Seq(ex1, ex2, ex3) ) )
  }

  test( "Assignments" ) {
    val ex1 = tla.primeInSingleton(n_x, 1)
    val ex2 = tla.primeInSingleton( n_x, tla.primeInSingleton(n_x, 2) )

    assert( correctRecursiveApplication( Seq(ex1, ex2) ) )
  }

  test( "Real spec" ) {
    val spec = specFromFile( "Paxos.tla" )

    assert( correctRecursiveApplication( Seq(spec) ) )
  }
}

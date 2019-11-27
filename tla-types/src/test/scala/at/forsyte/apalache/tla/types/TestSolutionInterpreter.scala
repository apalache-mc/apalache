package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.smt.{SmtVarGenerator, Z3TypeSolver}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestSolutionInterpreter extends FunSuite with TestingPredefs with BeforeAndAfter {

  import at.forsyte.apalache.tla.lir.{Builder => tla}

  val useSoftConstraints = false
  val primeConsistency   = false

  var solutionInterpreter : SolutionInterpreter = new SolutionInterpreter( new TypeVarGenerator )
  var smtVarGen                                 = new SmtVarGenerator
  var solver                                    = new Z3TypeSolver( useSoftConstraints = useSoftConstraints )

  before {
    solutionInterpreter = new SolutionInterpreter( new TypeVarGenerator )
    smtVarGen = new SmtVarGenerator
    solver = new Z3TypeSolver( useSoftConstraints = useSoftConstraints )
  }

  test( "Example from the documentation" ) {
    // A(p,q) == p = p /\ q = q // Expected <T1, T2> => Bool
    val declA = tla.declOp( "A",
      tla.and(
        tla.eql( n_p, n_p ),
        tla.eql( n_q, n_q )
      ),
      "p", "q"
    )

    val globNC : GlobalNameContext = Map.empty

    def genT( declNext : TlaOperDecl ) : TlaType = {

      val globBM = BodyMapFactory.makeFromDecls( Seq( declA, declNext ) )
      val udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )

      val e = smtVarGen.getFresh
      val templ = udtg.makeTemplate( List.empty, declNext.body )
      val templApp = templ( e +: Nil )

      val ret = solver.solve( smtVarGen.allVars, templApp )
      assert( ret.nonEmpty )
      val solution = ret.get
      val ctx = udtg.getCtx

      val backMap = aux.uidToExMap( declA.body ) ++ aux.uidToExMap( declNext.body )

      solutionInterpreter.generalizeType( declA.name, backMap, ctx, solution )
    }

    val declNext1 = tla.declOp( "Next",
      tla.and(
        tla.appDecl( declA, tla.int( 1 ), tla.int( 2 ) ),
        tla.appDecl( declA, tla.str( "s" ), tla.str( "t" ) )
      )
    )

    val genT1 = genT( declNext1 )

    val assertCond1 = genT1 match {
      case OperT( TupT( TypeVar( i ), TypeVar( j ) ), BoolT ) => i == j
      case _ => false
    }

    assert( assertCond1 )

    val declNext2 = tla.declOp( "Next",
      tla.and(
        tla.appDecl( declA, tla.int( 1 ), tla.int( 2 ) ),
        tla.appDecl( declA, tla.str( "s" ), tla.str( "t" ) ),
        tla.appDecl( declA, tla.int( 1 ), tla.str( "t" ) )
      )
    )

    val genT2 = genT( declNext2 )

    val assertCond2 = genT2 match {
      case OperT( TupT( TypeVar( i ), TypeVar( j ) ), BoolT ) => i != j
      case _ => false
    }

    assert( assertCond2 )
  }

  test( "Generalization: Simple polymorphic operator" ) {
    val tautDecl = tla.declOp(
      "Taut",
      tla.eql( n_p, n_p ),
      "p"
    )

    /**
      * Taut(p) == p = p
      * Next == Taut(1) /\ Taut("a")
      */
    val nextBody =
      tla.and(
        tla.appDecl( tautDecl, tla.int( 1 ) ),
        tla.appDecl( tautDecl, tla.str( "a" ) )
      )

    val globNC : GlobalNameContext = Map.empty

    val globBM = BodyMapFactory.makeFromDecl( tautDecl )
    val udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )

    val e = smtVarGen.getFresh
    val templ = udtg.makeTemplate( List.empty, nextBody )
    val templApp = templ( e +: Nil )

    val ret = solver.solve( smtVarGen.allVars, templApp )
    assert( ret.nonEmpty )
    val solution = ret.get
    val ctx = udtg.getCtx

    val backMap = aux.uidToExMap( nextBody ) ++ aux.uidToExMap( tautDecl.body )

    val genT = solutionInterpreter.generalizeType( tautDecl.name, backMap, ctx, solution )

    // Expected: genT = < T > => BoolT
    val assertCond = genT match {
      case OperT( TupT( _ : TypeVar ), BoolT ) => true
      case _ => false
    }

    assert( assertCond )
  }

  test( "Generalization: Harder polymorphic operator" ) {
    val polyOperDecl = tla.declOp(
      "O",
      tla.ite( tla.eql( n_a, n_c ), n_b, tla.plus( n_b, 1 ) ),
      "a", "b", "c"
    )

    /**
      * O(a,b,c) == IF a = c
      * THEN b
      * ELSE b + 1
      * Next == O("a", 1, c) >= O( 1, 1, 1 ) + O( [a -> 1, b-> 2], 1, [a -> 1, c -> 3] )
      */
    val nextBody = tla.ge(
      tla.appDecl( polyOperDecl, tla.str( "a" ), tla.int( 1 ), tla.str( "c" ) ),
      tla.plus(
        tla.appDecl( polyOperDecl, tla.int( 1 ), tla.int( 1 ), tla.int( 1 ) ),
        tla.appDecl( polyOperDecl,
          tla.enumFun( tla.str( "a" ), tla.int( 1 ), tla.str( "b" ), tla.int( 2 ) ),
          tla.int( 1 ),
          tla.enumFun( tla.str( "a" ), tla.int( 1 ), tla.str( "c" ), tla.int( 3 ) )
        )
      )
    )

    val globNC : GlobalNameContext = Map.empty

    val globBM = BodyMapFactory.makeFromDecl( polyOperDecl )
    val udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )

    val e = smtVarGen.getFresh
    val templ = udtg.makeTemplate( List.empty, nextBody )
    val templApp = templ( e +: Nil )

    val ret = solver.solve( smtVarGen.allVars, templApp )
    assert( ret.nonEmpty )
    val solution = ret.get
    val ctx = udtg.getCtx

    val backMap = aux.uidToExMap( nextBody ) ++ aux.uidToExMap( polyOperDecl.body )

    val genT = solutionInterpreter.generalizeType( polyOperDecl.name, backMap, ctx, solution )

    // Expected: genT = < T, IntT, T > => IntT
    val assertCond = genT match {
      case OperT( TupT( t : TypeVar, IntT, t2 : TypeVar ), IntT ) => t == t2
      case _ => false
    }

    assert( assertCond )
  }

  test( "Recovery: No generalization" ) {
    val varDecls = List(
      TlaVarDecl( "x" ),
      TlaVarDecl( "y" )
    )
    val constDecls = List(
      TlaConstDecl( "N" )
    )

    val plusDecl = tla.declOp(
      "Plus",
      tla.plus( n_p, tla.name( "N" ) ),
      "p", "q"
    )

    val nextBody =
      tla.and(
        tla.unchanged( n_y ),
        tla.primeEq( n_x, tla.appDecl( plusDecl, n_x, n_y ) )
        //        tla.primeInSingleton( n_x, tla.appDecl( plusDecl, n_x, n_y ) )
      )

    val nextDecl = tla.declOp( "Next", nextBody )

    val globNC = new NameContextBuilder( smtVarGen ).build(
      varDecls ++ constDecls,
      primeConsistency = primeConsistency
    )

    val globBM = BodyMapFactory.makeFromDecls( Seq( plusDecl, nextDecl ) )
    val udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )

    val e = smtVarGen.getFresh
    val templ = udtg.makeTemplate( List.empty, nextBody )
    val templApp = templ( e +: Nil )

    val ret = solver.solve( smtVarGen.allVars, templApp )
    assert( ret.nonEmpty )
    val solution = ret.get
    val ctx = udtg.getCtx

    val recovered = solutionInterpreter.interpret(
      Map( nextDecl.name -> BoolT ),
      globBM,
      ctx,
      globNC,
      solution
    )

    val assertCond = recovered forall {
      case ("x", t) => t == IntT
      case ("y", t) => t == recovered( "y'" )
      case (s, t) if s == plusDecl.name => t match {
        case OperT( TupT( IntT, _ ), IntT ) => true
        case _ => false
      }
      case _ => true
    }
    assert( assertCond )
  }

  test( "Recovery: Using generalization" ) {
    val polyOperDecl = tla.declOp(
      "O",
      tla.ite( tla.eql( n_a, n_c ), n_b, tla.plus( n_b, 1 ) ),
      "a", "b", "c"
    )

    /**
      * O(a,b,c) == IF a = c
      * THEN b
      * ELSE b + 1
      * Next == O("a", 1, c) >= O( 1, 1, 1 ) + O( [a -> 1, b-> 2], 1, [a -> 1, c -> 3] )
      */
    val nextBody = tla.ge(
      tla.appDecl( polyOperDecl, tla.str( "a" ), tla.int( 1 ), tla.str( "c" ) ),
      tla.plus(
        tla.appDecl( polyOperDecl, tla.int( 1 ), tla.int( 1 ), tla.int( 1 ) ),
        tla.appDecl( polyOperDecl,
          tla.enumFun( tla.str( "a" ), tla.int( 1 ), tla.str( "b" ), tla.int( 2 ) ),
          tla.int( 1 ),
          tla.enumFun( tla.str( "a" ), tla.int( 1 ), tla.str( "c" ), tla.int( 3 ) )
        )
      )
    )

    val nextDecl = tla.declOp( "Next", nextBody )

    val globNC : GlobalNameContext = Map.empty

    val globBM = BodyMapFactory.makeFromDecls( Seq( polyOperDecl, nextDecl ) )
    val udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )

    val e = smtVarGen.getFresh
    val templ = udtg.makeTemplate( List.empty, nextBody )
    val templApp = templ( e +: Nil )

    val ret = solver.solve( smtVarGen.allVars, templApp )
    assert( ret.nonEmpty )
    val solution = ret.get
    val ctx = udtg.getCtx

    val recovered = solutionInterpreter.interpret(
      Map( nextDecl.name -> BoolT ),
      globBM,
      ctx,
      globNC,
      solution
    )

    val assertCond = recovered forall {
      case (s, t) if s == polyOperDecl.name => t match {
        case OperT( TupT( t1, IntT, t2 ), IntT ) => t1 == t2
        case _ => false
      }
      case _ => true
    }
    assert( assertCond )

  }

}

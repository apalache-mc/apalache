package at.forsyte.apalache.tla.types.smt

import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, BoolFormula, Or}
import at.forsyte.apalache.tla.types.Names._
import at.forsyte.apalache.tla.types._
import at.forsyte.apalache.tla.types.smt.FunWrappers.{HasAtFunWrapper, SizeFunWrapper}
import com.microsoft.z3._

object Z3TypeSolver {
  type Solution = SmtDatatype => TlaType
}

/**
  * Z3TypeSolver
  */
class Z3TypeSolver( useSoftConstraints : Boolean ) {
  import Z3TypeSolver._

  private val ctx           : Context          = new Context
  private val solver        : Z3Solver         =
    if ( useSoftConstraints ) new MaxSMTSolver( ctx )
    else new ClassicSolver( ctx )
  private val strEnumerator : StringEnumerator = new StringEnumerator

  /************
   *INIT BEGIN*
   ************/

  private val intS  : Sort = ctx.getIntSort
  private val boolS : Sort = ctx.getBoolSort

  /**
    * Initialize datatype
    */
  private val intTCtor  : Constructor =
    ctx.mkConstructor( intTName, s"is$intTName", null, null, null )
  private val strTCtor  : Constructor =
    ctx.mkConstructor( strTName, s"is$strTName", null, null, null )
  private val boolTCtor : Constructor =
    ctx.mkConstructor( boolTName, s"is$boolTName", null, null, null )
  private val setTCtor  : Constructor =
    ctx.mkConstructor( setTName, s"is$setTName", Array( "st" ), Array[Sort]( null ), Array( 0 ) )
  private val seqTCtor  : Constructor =
    ctx.mkConstructor( seqTName, s"is$seqTName", Array( "sq" ), Array[Sort]( null ), Array( 0 ) )
  private val funTCtor  : Constructor =
    ctx.mkConstructor( funTName, s"is$funTName", Array( "dom", "cdm" ), Array[Sort]( null, null ), Array( 0, 0 ) )
  private val operTCtor : Constructor =
    ctx.mkConstructor( operTName, s"is$operTName", Array( "odom", "ocdm" ), Array[Sort]( null, null ), Array( 0, 0 ) )
  private val tupTCtor  : Constructor =
    ctx.mkConstructor( tupTName, s"is$tupTName", Array( "i" ), Array[Sort]( intS ), null )
  private val recTCtor  : Constructor =
    ctx.mkConstructor( recTName, s"is$recTName", Array( "r" ), Array[Sort]( intS ), null )
  private val varTCtor  : Constructor =
    ctx.mkConstructor( varTName, s"is$varTName", Array( "j" ), Array[Sort]( intS ), null )

  private val tlaTypeDTS : DatatypeSort =
    ctx.mkDatatypeSort(
      dtName,
      Array(
        intTCtor, strTCtor, boolTCtor, setTCtor, seqTCtor,
        funTCtor, operTCtor, tupTCtor, recTCtor, varTCtor
      )
    )

  /**
    * Declare functions
    */
  private val sizeOfDecl   : FuncDecl = ctx.mkFuncDecl( sizeOfName, intS, intS )
  private val hasIdxDecl   : FuncDecl = ctx.mkFuncDecl( hasIndexName, Array[Sort]( intS, intS ), boolS )
  private val atIdxDecl    : FuncDecl = ctx.mkFuncDecl( atIndexName, Array[Sort]( intS, intS ), tlaTypeDTS )
  private val hasFieldDecl : FuncDecl = ctx.mkFuncDecl( hasFieldName, Array[Sort]( intS, intS ), boolS )
  private val atFieldDecl  : FuncDecl = ctx.mkFuncDecl( atFieldName, Array[Sort]( intS, intS ), tlaTypeDTS )

  /**
    * Axioms
    */
//  private val axiomSizeOf : BoolExpr = {
//    val i = ctx.mkConst( ctx.mkSymbol( "i" ), intS )
//    val j = ctx.mkConst( ctx.mkSymbol( "j" ), intS )
//    ctx.mkForall(
//      Array[Expr]( i, j ),
//      ctx.mkImplies(
//        ctx.mkApp( hasIdxDecl, i, j ).asInstanceOf[BoolExpr],
//        ctx.mkGe( ctx.mkApp( sizeOfDecl, i ).asInstanceOf[ArithExpr], j.asInstanceOf[ArithExpr] )
//      ),
//      0, null, null, null, null
//    )
//  }
//  solver.assert( axiomSizeOf )

  /**********
   *INIT END*
   **********/

  /**
    * Contains methods for the conversion between our internal representation and z3's Expr/BoolExpr classes
    */
  private object Z3Converter {
    def dtToSmt( dt : SmtDatatype ) : Expr = dt match {
      case `int` => ctx.mkApp( intTCtor.ConstructorDecl )
      case `str` => ctx.mkApp( strTCtor.ConstructorDecl )
      case `bool` => ctx.mkApp( boolTCtor.ConstructorDecl )
      case set( x ) => ctx.mkApp( setTCtor.ConstructorDecl, dtToSmt( x ) )
      case seq( x ) => ctx.mkApp( seqTCtor.ConstructorDecl, dtToSmt( x ) )
      case fun( x, y ) => ctx.mkApp( funTCtor.ConstructorDecl, dtToSmt( x ), dtToSmt( y ) )
      case oper( x, y ) => ctx.mkApp( operTCtor.ConstructorDecl, dtToSmt( x ), dtToSmt( y ) )
      case tup( i ) => ctx.mkApp( tupTCtor.ConstructorDecl, varToConst( i ) )
      case rec( i ) => ctx.mkApp( recTCtor.ConstructorDecl, varToConst( i ) )
      case f : SmtTypeVariable => varToConst( f )
    }

    def bfToSmt( bf : BoolFormula ) : BoolExpr = bf match {
      case And( args@_* ) => ctx.mkAnd( args map bfToSmt : _* )
      case Or( args@_* ) => ctx.mkOr( args map bfToSmt : _* )
      case Eql( lhs, rhs ) => ctx.mkEq( dtToSmt( lhs ), dtToSmt( rhs ) )
      case hasField( v, s, t ) =>
        val vConst = varToConst( v )
        val sId = strEnumerator.add( s )
        val sInt = ctx.mkInt( sId )
        val exists = ctx.mkApp( hasFieldDecl, vConst, sInt ).asInstanceOf[BoolExpr]
        val value = ctx.mkEq( ctx.mkApp( atFieldDecl, vConst, sInt ), dtToSmt( t ) )
        ctx.mkAnd( exists, value )
      case hasIndex( v, i, t ) =>
        val vConst = varToConst( v )
        val iInt = ctx.mkInt( i )
        val exists = ctx.mkApp( hasIdxDecl, vConst, iInt ).asInstanceOf[BoolExpr]
        val value = ctx.mkEq( ctx.mkApp( atIdxDecl, vConst, iInt ), dtToSmt( t ) )
        // Explicit instantiation
        val sizeAxiom = ctx.mkGe( ctx.mkApp( sizeOfDecl, vConst ).asInstanceOf[ArithExpr], iInt )
        ctx.mkAnd( exists, value, sizeAxiom )
      case sizeOfEql( i, j ) =>
        ctx.mkEq( ctx.mkApp( sizeOfDecl, varToConst( i ) ), ctx.mkInt( j ) )
      case _ =>
        throw new IllegalArgumentException( "..." )
    }

    /**
      * Standard string representation
      */
    def varToSmtName( v : SmtVariable ) : String = v match {
      case SmtIntVariable( i ) => s"${Names.intVarSymb}$i"
      case SmtTypeVariable( f ) => s"${Names.tVarSymb}$f"
    }

    /**
      * Transforms a SmtVariable to its corresponding z3 Expr (of the correct sort)
      */
    def varToConst( v : SmtVariable ) : Expr =
      ctx.mkConst( varToSmtName( v ), v match {
        case _ : SmtIntVariable => intS
        case _ : SmtTypeVariable => tlaTypeDTS
      } )
  }

  /**
    * Solves for TlaTypes
    */
  def solve(
             vars : Seq[SmtVariable],
             constraints : BoolFormula
           ) : Option[Solution] = {
    solver.push()
    addVars( vars )
    addConstraints( constraints )
    val status = solver.check()
    val model = solver.getModel
    solver.pop()
    status match {
      case Status.SATISFIABLE =>
        val sizeWrap = SizeFunWrapper( ctx, model, sizeOfDecl )
        val idxWrap = HasAtFunWrapper( ctx, model, hasIdxDecl, atIdxDecl )
        val fieldWrap = HasAtFunWrapper( ctx, model, hasFieldDecl, atFieldDecl )

        val typeReconstructor = new TypeReconstructor( idxWrap.apply, fieldWrap.apply, sizeWrap.apply, strEnumerator )

        def solution( dt: SmtDatatype ) : TlaType = {
          val expr = Z3Converter.dtToSmt( dt )
          typeReconstructor( model.eval(
            expr,
            false // completion:  When this flag is enabled, a model value will be assigned to any constant or function that does not have an interpretation in the model.
            /* TODO: Investigate potential benefits of completion = true */
          ) )
        }

        Some( solution )
      case _ => None
    }
  }

  /**
    * Adds all variable declarations (both Int and tlaT) to the solver.
    * Soft asserts that all tlaT variables have the form (varT x). The soft assert is a no-op
    * when using ClassicSolver, i.e. when useSoftConstraints = false
    *
    * Returns the list of all tlaT variable (function) declarations.
    */
  private def addVars( vars : Seq[SmtVariable] ) : Seq[FuncDecl] =
    vars flatMap {
      case x : SmtIntVariable =>
        ctx.mkConstDecl( Z3Converter.varToSmtName( x ), intS )
        None
      case x@SmtTypeVariable( f ) =>
        val v = ctx.mkConstDecl( Z3Converter.varToSmtName( x ), tlaTypeDTS )
        solver.assertSoft(
          ctx.mkEq(
            ctx.mkConst( v ),
            ctx.mkApp( varTCtor.ConstructorDecl, ctx.mkInt( f ) )
          ),
          1, // default weight
          "" // no label
        )
        Some( v )
    }

  /**
    * Asserts the constraints specified by constraints (typically an And(...) formula)
    */
  private def addConstraints( constraints : BoolFormula ) : Unit = {
    val flatConstraints = flatten( constraints )
    flatConstraints foreach { bf =>
      solver.assert( Z3Converter.bfToSmt( bf ) )
    }
  }

  /**
    * Decomposes And(...) formulas into a sequence of formulas
    */
  private def flatten( s : BoolFormula ) : Seq[BoolFormula] = s match {
    case And( conds@_* ) => conds flatMap flatten
    case z => Seq( z )
  }
}

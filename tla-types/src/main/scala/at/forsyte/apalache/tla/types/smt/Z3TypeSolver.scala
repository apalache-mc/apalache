package at.forsyte.apalache.tla.types.smt

import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, BoolFormula, Or}
import at.forsyte.apalache.tla.types.Names._
import at.forsyte.apalache.tla.types._
import com.microsoft.z3._

object Z3TypeSolver {
  type SolutionFunction = SmtDatatype => TlaType
  abstract class SolutionOrUnsatCore {
    def nonEmpty : Boolean = this match {
      case _ : Solution => true
      case _ => false
    }
  }
  sealed case class UnsatCore( core: Array[BoolExpr] ) extends SolutionOrUnsatCore
  sealed case class Solution( f: SolutionFunction ) extends SolutionOrUnsatCore
}

/**
  * Z3TypeSolver
  */
class Z3TypeSolver( useSoftConstraints : Boolean, tvg: TypeVarGenerator, specLimits: SpecLimits ) {
  import Z3TypeSolver._

  private val ctx           : Context          = new Context
  private val solver        : Z3Solver         =
    if ( useSoftConstraints ) new MaxSMTSolver( ctx )
    else new ClassicSolver( ctx )
  private val enum : Enumeration = specLimits.getEnumeration
//  private val strEnumerator : StringEnumerator = new StringEnumerator

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
  private val operTCtor : Constructor = {
    val M = specLimits.maxIndex
    val idxNames = ( 1 to M ).toArray map { i => s"oidx$i" }
    val names = ( "osz" +: idxNames ) :+ "ocdm"

    val sorts : Array[Sort] = intS +: Array.fill( M + 1 )( null )
    val sortRefs = Array.fill( M + 2 )( 0 )

    ctx.mkConstructor( operTName, s"is$operTName", names, sorts, sortRefs)
  }
  private val tupTCtor  : Constructor = {
    val M = specLimits.maxIndex
    val idxNames = (1 to M).toArray map { i => s"idx$i" }
    val names =  "sz" +: idxNames

    val sorts : Array[Sort] = intS +: Array.fill( M )( null )
    val sortRefs = Array.fill( M + 1 )( 0 )

    ctx.mkConstructor( tupTName, s"is$tupTName", names, sorts, sortRefs )
  }
  private val recTCtor  : Constructor = {
    val N = specLimits.maxNumFields
    val idxNames = (1 to N).toArray map { i => s"fld$i" }
    val names =  "id" +: idxNames

    val sorts : Array[Sort] = intS +: Array.fill( N )( null )
    val sortRefs = Array.fill( N + 1 )( 0 )

    ctx.mkConstructor( recTName, s"is$recTName", names, sorts, sortRefs )
  }
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
      case tup( size, is ) =>
        val sizeTerm = size match {
        case i: SmtIntVariable => varToConst( i )
        case SmtKnownInt( i ) => ctx.mkInt( i )
      }
        val indices = is map dtToSmt
        ctx.mkApp( tupTCtor.ConstructorDecl, sizeTerm +: indices : _* )
      case oper( tup( size, is ), cdm ) =>
        val sizeTerm = size match {
          case i: SmtIntVariable => varToConst( i )
          case SmtKnownInt( i ) => ctx.mkInt( i )
        }
        val indices = is map dtToSmt
        ctx.mkApp( operTCtor.ConstructorDecl, ( sizeTerm +: indices ) :+ dtToSmt( cdm ) : _* )
      case rec( id, fs ) =>
        val fields = fs map dtToSmt
        ctx.mkApp( recTCtor.ConstructorDecl, varToConst( id ) +: fields : _* )
      case f : SmtTypeVariable => varToConst( f )
    }

    def bfToSmt( bf : BoolFormula ) : BoolExpr = bf match {
      case And( args@_* ) => ctx.mkAnd( args map bfToSmt : _* )
      case Or( args@_* ) => ctx.mkOr( args map bfToSmt : _* )
      case Eql( lhs, rhs ) => ctx.mkEq( dtToSmt( lhs ), dtToSmt( rhs ) )
      case ge( i, j ) => ctx.mkGe( varToConst( i ).asInstanceOf[ArithExpr], ctx.mkInt( j ) )
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
             constraints : BoolFormula,
             observedFieldOpt : Option[Map[SmtIntVariable, Set[String]]] = None
           ) : SolutionOrUnsatCore = {
    addVars( vars )
    addConstraints( constraints )
    val status = solver.check()
    status match {
      case Status.SATISFIABLE =>
        val model = solver.getModel

        val idxEval = new IndexEvaluator {
          override def getValue( i : Int ) : Int = model.eval(
            ctx.mkConst( s"${Names.intVarSymb}$i", intS ),
            true
          ).asInstanceOf[IntNum].getInt
        }

        val narrowerOpt = observedFieldOpt.map( new TypeNarrower( _, idxEval ) )

        val recovery = new TypeRecovery( tvg, specLimits, narrowerOpt )

        def solutionFn( dt: SmtDatatype ) : TlaType = {
          val expr = Z3Converter.dtToSmt( dt )
          val evalEx = model.eval(
            expr,
            true // completion:  When this flag is enabled, a model value will be assigned to any constant or function that does not have an interpretation in the model.
            /* TODO: Investigate if true is useful for partial specifications, where some values are still undefined */
          )
          recovery( evalEx )
        }

        Solution( solutionFn )
      case _ =>
        UnsatCore( solver.getUnsatCore )
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
        val v = ctx.mkConstDecl( Z3Converter.varToSmtName( x ), intS )
        // Soft constraint : each intVar is unique (e.g. equal to its id)
        // This makes record identifiers as distinct as possible, allowing for
        // more precise field recovery
        solver.assertSoft(
          ctx.mkEq(
            ctx.mkConst( v ),
            ctx.mkInt( x.id )
          ),
          1, // default weight
          "" // no label
        )
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

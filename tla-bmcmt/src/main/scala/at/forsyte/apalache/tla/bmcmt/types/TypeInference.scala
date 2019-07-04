package at.forsyte.apalache.tla.bmcmt.types

import java.math.RoundingMode

import at.forsyte.apalache.tla.bmcmt.{InternalCheckerError, InvalidTlaExException, TypeException}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import com.google.common.math.IntMath
import box.setlike.DisjointSets
import box.setlike.DisjointSets.DJSState
import scalaz._
import Scalaz._
import at.forsyte.apalache.tla.lir.io.UTFPrinter

object CounterStates {
  type CounterType = Int
  type CounterState[T] = State[CounterType, T]

  def inc( ) : CounterState[CounterType] = State[CounterType, CounterType] {
    s => (s + 1, s)
  }
}

object Signatures {

  import CounterStates._

  sealed case class Signature( typeParams : List[TypeParam], args : List[CellT], res : CellT ) {

    override def toString : String = {
      val ts = typeParams map {
        _.signature
      } mkString ", "
      val as = args map {
        _.signature
      } mkString s" ${UTFPrinter.m_times} "
      val prefix = if ( typeParams.isEmpty ) "" else s"${UTFPrinter.m_forall} ${ts} . "
      s"${prefix}${as} ${UTFPrinter.m_rarrow} ${res.signature}"
    }
  }

  private def typeParam( exId : UID, id : Int ) : TypeParam = TypeParam( s"${exId.id}_${id}" )

  def get( op : OperEx ) : Signature = getFresh( op ).run( 0 )._2

  def getFresh( op : OperEx ) : CounterState[Signature] = inc() map { i =>
    val exId = op.ID
    val T = TypeParam( s"c${i}" )

    def ts( n : Int ) : List[TypeParam] = List.range( 1, n + 1 ) map { j =>
      TypeParam( s"c${i}_${j}" )
    }

    val ts2 = ts( 2 )

    val List( t1, t2 ) = ts2

    val ret = op.oper match {
      // Logic
      /** TODO: Introduce AnyArity and/or */
      case TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.implies | TlaBoolOper.equiv =>
        Signature( List.empty, List.fill( 2 )( BoolT() ), BoolT() )
      case TlaBoolOper.not =>
        Signature( List.empty, List( BoolT() ), BoolT() )
      case TlaBoolOper.exists | TlaBoolOper.forall =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), BoolT() )
      case TlaOper.chooseBounded =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), OptT( T ) )
      case TlaOper.chooseIdiom =>
        Signature( List( T ), List( FinSetT( T ) ), OptT( T ) )

      // Arithmetic
      case TlaArithOper.plus | TlaArithOper.minus | TlaArithOper.mult | TlaArithOper.div | TlaArithOper.mod =>
        Signature( List.empty, List( IntT(), IntT() ), IntT() )
      case TlaArithOper.dotdot =>
        Signature( List.empty, List( IntT(), IntT() ), FinSetT( IntT() ) )
      case TlaArithOper.lt | TlaArithOper.gt | TlaArithOper.le | TlaArithOper.ge =>
        Signature( List.empty, List( IntT(), IntT() ), BoolT() )

      // Sets
      case TlaOper.eq | TlaOper.ne | TlaSetOper.in | TlaSetOper.notin | TlaSetOper.subseteq =>
        Signature( ts2, ts2, BoolT() )
      case TlaSetOper.cap | TlaSetOper.cup | TlaSetOper.setminus =>
        Signature( List( T ), List.fill( 2 )( FinSetT( T ) ), FinSetT( T ) )
      case TlaSetOper.enumSet =>
        Signature( List( T ), List.fill( op.args.size )( T ), FinSetT( T ) )
      case TlaSetOper.filter =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), FinSetT( T ) )
      case TlaSetOper.map =>
        Signature( ts2, List( t1, t2, FinSetT( t2 ) ), FinSetT( t1 ) )
      case TlaSetOper.powerset =>
        Signature( List( T ), List( FinSetT( T ) ), PowSetT( FinSetT( T ) ) )
      case TlaSetOper.union =>
        Signature( List( T ), List( FinSetT( FinSetT( T ) ) ), FinSetT( T ) )

      // Functions
      case TlaFunOper.app =>
        Signature( ts2, List( FunT( FinSetT( t1 ), t2 ), t1 ), t2 )
      case TlaFunOper.domain =>
        Signature( ts2, List( FunT( t1, t2 ) ), t1 )
      case TlaFunOper.funDef =>
        val n = IntMath.divide( op.args.size, 2, RoundingMode.CEILING ) // ceil( n/2 ) type params
      val nTs = ts( n )
        Signature( nTs, nTs.head :: ( nTs.tail flatMap { t => List( t, FinSetT( t ) ) } ), FunT( CrossProdT( nTs.tail map FinSetT ), nTs.head ) )
      case TlaSetOper.funSet =>
        Signature( ts2, ts2 map FinSetT, FinFunSetT( FinSetT( t1 ), FinSetT( t2 ) ) )
      case TlaFunOper.except =>
        // except takes 2n + 1 args, the 1st is the function, followed by n element-set pairs
        val n = ( op.args.size - 1 ) / 2
        Signature( ts2, FunT( FinSetT( t1 ), t2 ) +: List.fill( n )( ts2 ).flatten, FunT( FinSetT( t1 ), t2 ) )

      // Records
      // TBA

      // Control
      case TlaControlOper.ifThenElse =>
        Signature( List( T ), List( BoolT(), T, T ), T )
      case TlaControlOper.caseNoOther =>
        Signature( List( T ), List.fill( op.args.size / 2 )( List( BoolT(), T ) ).flatten, OptT( T ) )
      case TlaControlOper.caseWithOther =>
        // CWO takes 2n + 1 args, the 1st is the OTHER, followed by n predicate-branchVal pairs
        val n = ( op.args.size - 1 ) / 2
        Signature( List( T ), T +: List.fill( n )( List( BoolT(), T ) ).flatten, T )

      // Actions
      case TlaActionOper.prime => // The generic prime accepts any input type and can yield any output type
        Signature( ts2, List( t1 ), t2 )

      case _ =>
        throw new InternalCheckerError( s"Signature for operator [${op.oper.name}] is not implemented" )
      //        Signature( List.empty, List.empty, UnknownT() )
    }
    assert( op.oper.isCorrectArity( ret.args.size ) )
    ret
  }

}

object TypeInference {

  import CounterStates._

  sealed case class isType( v1 : CellT, v2 : CellT )

  def smtVar( id : UID ) : TypeParam = TypeParam( s"b_${id.id}" )

  def smtVar( ex : TlaEx ) : TypeParam = smtVar( ex.ID )

  private def thetaInternal( tlaEx : TlaEx ) : CounterState[List[isType]] = tlaEx match {
    case NullEx =>
      throw new InvalidTlaExException( "NullEx present during type inference step", tlaEx )
    case ValEx( value ) =>
      val terminalType = value match {
        case TlaInt( _ ) => IntT()
        case TlaBool( _ ) => BoolT()
        case TlaStr( _ ) => ConstT()
        case _ =>
          throw new InvalidTlaExException( "Tla value type not supported", tlaEx )
      }
      List( isType( smtVar( tlaEx ), terminalType ) ).point[CounterState]

    case NameEx( n ) =>
      List( isType( smtVar( tlaEx ), TypeParam( s"${n}" ) ) ).point[CounterState]
    case ex@OperEx( TlaActionOper.prime, NameEx( n ) ) => // if we see x' the smt var for the current expression must be consistent with the type of x' overall
      List( isType( smtVar( ex ), TypeParam( s"${n}'" ) ) ).point[CounterState]
    case ex : OperEx => for {
      sig <- Signatures getFresh ex
      bl = smtVar( ex )
      bls = ex.args map smtVar
      subThetas <- ex.args.toList.traverseS( thetaInternal ).map {
        _.flatten
      }
    } yield isType( bl, sig.res ) +: ( bls.zip( sig.args ) map { case (a, b) => isType( a, b ) } ) ++: subThetas
    //    case _ => List.empty[isType].point[CounterState]
  }

  def theta( tlaEx : TlaEx ) : List[isType] = thetaInternal( tlaEx ).run( 0 )._2

  def incompatible( a : CellT, b : CellT ) : Boolean = false

  def max( a : CellT, b : CellT ) : CellT = (a,b) match {
    case ( TypeParam(_), _) => b
    case ( _, TypeParam(_)) => a
    case _ => a.unify( b ).get
  }

  private def trace( v : CellT, map : Map[CellT, CellT] ) : State[DisjointSets[CellT], CellT] =
    v match {
      case TypeParam(_) =>
        DisjointSets.findComputation( v ) map { p =>
          map.get( p ) match {
            case None => p
            case Some(TypeParam(_)) => p
            case Some(c) => c
          }
        }
      case FunT( a, b ) => for {
        v1 <- trace(a, map)
        v2 <- trace(b, map)
      } yield FunT(v1,v2)
      case FinSetT(x) =>
        trace(x, map) map FinSetT
      case _ => State[DisjointSets[CellT], CellT] { s => (s,v) }
    }

//    for {
//    p <- DisjointSets.findComputation( v )
//    mapv = map.getOrElse( p, p )
//    ret <- if ( mapv == p )
//      gets[DisjointSets[CellT], CellT] { _ =>
//        println(1)
//        p
//      }
//    else {
//      println( 2 )
//      trace( mapv, map +:  )
//    }
//  } yield ret

  private def expand( map: Map[CellT, CellT], djs: DisjointSets[CellT] ) : Map[CellT,CellT] = {
    val cmp = map.toList traverseS {
      case (k,v) => trace(v, map) map { k -> _ }
    }
    cmp.run(djs)._2.toMap
  }

  def apply( tlaEx : TlaEx ) : Map[CellT, CellT] = { // to be Map[UID, CellT]
    type M = Map[CellT, CellT]
    type D = DisjointSets[CellT]
    sealed case class internal( m : M, d : D, c : CounterType )
    type MD = internal
    type internalState[T] = State[MD, T]

    def internalFind( el : CellT ) : internalState[CellT] = State[MD, CellT] {
      st =>
        val (newD, e) = st.d.find( el )
        (st.copy( d = newD ), e)
    }

    def internalUnion( el1 : CellT, el2 : CellT ) : internalState[CellT] = State[MD, CellT] {
      st =>
        val (newD, e) = st.d.union( el1, el2 )
        (st.copy( d = newD ), e)
    }

    def internalInc( ) : internalState[CounterType] = State[MD, CounterType] {
      st =>
        (st.copy( c = st.c + 1 ), st.c)
    }

    def internalGOE( el : CellT ) : internalState[CellT] =
    //      for {
    //        mapEl <- gets[MD, Option[CellT]] {
    //          _.m.get( el )
    //        }
    //        ret <- mapEl match {
    //          case Some( x ) => x.point[internalState]
    //          case None => internalInc() map {
    //            i => TypeParam( s"T${i}" )
    //          }
    //        }
    //      } yield ret
      gets[MD, CellT] {
        st => st.m.getOrElse( el, el )
      }

    def internalUpdate( k : CellT, v : CellT ) : internalState[Unit] = modify[MD] {
      st => st.copy( m = st.m + ( k -> v ) )
    }

    val queue = theta( tlaEx )

    //    println(queue)

    val cmp : internalState[List[Unit]] =
      queue traverseS { el =>
        for {
          //          el <- queue
          _ <- el match {
            case isType( v1 : TypeParam, v2 : TypeParam ) => for {
              rep1 <- internalFind( v1 )
              rep2 <- internalFind( v2 )
              t1 <- internalGOE( rep1 )
              t2 <- internalGOE( rep2 )

              _ = if ( incompatible( t1, t2 ) ) throw new TypeException( s"Types ${t1} and ${t2} are incompatible." )

              newT = max( t1, t2 )

              newRep <- internalUnion( rep1, rep2 )

              _ <- internalUpdate( newRep, newT )
            } yield ()
            case isType( v : TypeParam, c ) => for { // c not a typeparam for sure
              rep <- internalFind( v )
              t <- internalGOE( rep )

              _ = if ( incompatible( t, c ) ) throw new TypeException( s"Types ${c} and ${t} are incompatible." )

              newT = max( t, c )

              _ <- internalUpdate( rep, newT )

            } yield ()

            case isType( a, b ) => throw new TypeException( s"Types ${a} and ${b} are incompatible." )
          }
        } yield ()
      }

    val internal(endMap, endDJS,_) = cmp.run( internal( Map.empty, DisjointSets.empty, 0 ) )._1

    def lookup(map: M)(p: CellT) = map.get(endDJS.find( p )._2)

    val interesting = TypeParam("b_4")
    val cmpTrace = trace( interesting, Map( interesting -> endMap(interesting)) )

    val traceRes = cmpTrace.run(endDJS)._2

    println("----------------")
    println(traceRes)

    val ret = expand(endMap, endDJS)

    println( "----------" )

    println( lookup(ret)(TypeParam("x")))
    println( lookup(ret)(TypeParam("b_3")) ) // f
    println( lookup(ret)(TypeParam("c2_2") ) ) // f codom elems
//
    ret

//    endMap

  }

}

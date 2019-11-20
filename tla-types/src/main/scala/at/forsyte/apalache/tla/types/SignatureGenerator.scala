package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{OperEx, ValEx}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}

/**
  * Generates the signature (or all possible signatures) for a given built-in operator
  *
  * We assume the built-in operators have a known list of possible signatures.
  * The arguments are taken as OperEx, because this allows us to handle what
  * the paper describes as infinite families of fixed-arity operators (e.g. {...}),
  * where we can infer the arity (or in the case of records, the fields) from the OperEx arguments
  */
class SignatureGenerator {
  private val typeVarGenerator : TypeVarGenerator = new TypeVarGenerator

  def getPossibleSignatures( operEx : OperEx ) : List[PolyOperT] = operEx.oper match {
    /** Logic */
    // \A T . <T> => T
    case TlaOper.eq | TlaOper.ne =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( t, t ), BoolT ) ) )
    // \A n . <Bool^n> => Bool
    case TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.implies | TlaBoolOper.equiv =>
      List( PolyOperT( List.empty, OperT( TupT( List.fill( operEx.args.length )( BoolT ) : _* ), BoolT ) ) )
    // <Bool> => Bool
    case TlaBoolOper.not =>
      List( PolyOperT( List.empty, OperT( TupT( BoolT ), BoolT ) ) )
    // \A T . <T,Set(T),Bool> => Bool
    case TlaBoolOper.forall | TlaBoolOper.exists =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( t, SetT( t ), BoolT ), BoolT ) ) )

    /** Choose */
    // \A T . <T,Set(T),Bool> => T
    case TlaOper.chooseBounded =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( t, SetT( t ), BoolT ), t ) ) )

    /** Action */
//    case TlaActionOper.unchanged =>
//  SHOULD NEVER BE EVALUATED

    /** Arithmetic */
    case TlaArithOper.plus | TlaArithOper.minus | TlaArithOper.mult |
         TlaArithOper.div | TlaArithOper.mod =>
      List( PolyOperT( List.empty, OperT( TupT( IntT, IntT ), IntT ) ) )
    case TlaArithOper.uminus =>
      List( PolyOperT( List.empty, OperT( TupT( IntT ), IntT ) ) )
    case TlaArithOper.dotdot =>
      List( PolyOperT( List.empty, OperT( TupT( IntT, IntT ), SetT( IntT ) ) ) )
    case TlaArithOper.le | TlaArithOper.lt | TlaArithOper.ge | TlaArithOper.gt =>
      List( PolyOperT( List.empty, OperT( TupT( IntT, IntT ), BoolT ) ) )

    /** Sets */
    case TlaSetOper.in | TlaSetOper.notin =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( t, SetT( t ) ), BoolT ) ) )
    case TlaSetOper.supsetProper | TlaSetOper.subsetProper |
         TlaSetOper.supseteq | TlaSetOper.subseteq =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SetT( t ), SetT( t ) ), BoolT ) ) )
    case TlaSetOper.cup | TlaSetOper.cap | TlaSetOper.setminus =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SetT( t ), SetT( t ) ), SetT( t ) ) ) )
    case TlaSetOper.enumSet =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( List.fill( operEx.args.length )( t ) : _* ), SetT( t ) ) ) )
    case TlaSetOper.filter =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( t, SetT( t ), BoolT ), SetT( t ) ) ) )
    case TlaSetOper.map =>
      val n = ( operEx.args.length - 1 ) / 2
      val t = typeVarGenerator.getUnique
      val ts = typeVarGenerator.getNUnique( n )
      val allPairs = ts flatMap { x => List( x, SetT( x ) ) }
      List( PolyOperT( t +: ts, OperT( TupT( t +: allPairs : _* ), SetT( t ) ) ) )
    case TlaSetOper.powerset =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SetT( t ) ), SetT( SetT( t ) ) ) ) )
    case TlaSetOper.union =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SetT( SetT( t ) ) ), SetT( t ) ) ) )

    /** Functions */
    case TlaFunOper.domain =>
      val ts = typeVarGenerator.getNUnique( 2 )
      val List( t1, t2 ) = ts
      List( PolyOperT( ts, OperT( TupT( FunT( t1, t2 ) ), SetT( t1 ) ) ) )
    case TlaSetOper.funSet =>
      val ts = typeVarGenerator.getNUnique( 2 )
      val List( t1, t2 ) = ts
      List( PolyOperT( ts, OperT( TupT( SetT( t1 ), SetT( t2 ) ), SetT( FunT( t1, t2 ) ) ) ) )
    case TlaFunOper.funDef =>
      val n = ( operEx.args.length - 1 ) / 2
      val t = typeVarGenerator.getUnique
      val ts = typeVarGenerator.getNUnique( n )
      val allPairs = ts flatMap { x => List( x, SetT( x ) ) }
      List( PolyOperT( t +: ts, OperT( TupT( t +: allPairs : _* ), FunT( TupT( ts : _* ), t ) ) ) )

    /** Records */
    case TlaFunOper.enum =>
      val kvMap = operEx.args.zipWithIndex.collect {
        case (ValEx( TlaStr( s ) ), i) if i % 2 == 0 =>
          s -> typeVarGenerator.getUnique
      }.toMap

      val ts = kvMap.values.toList

      val tupArgs = ts flatMap { v => List( StrT, v ) }
      List( PolyOperT( ts, OperT( TupT( tupArgs : _* ), RecT( kvMap ) ) ) )

    case TlaSetOper.recSet =>
      val kvMap = operEx.args.zipWithIndex.collect {
        case (ValEx( TlaStr( s ) ), i) if i % 2 == 0 =>
          s -> typeVarGenerator.getUnique
      }.toMap

      val ts = kvMap.values.toList

      val tupArgs = ts flatMap { v => List( StrT, SetT( v ) ) }
      List( PolyOperT( ts, OperT( TupT( tupArgs : _* ), SetT( RecT( kvMap ) ) ) ) )

    /** Tuples */
    case TlaFunOper.tuple =>
      val ts = typeVarGenerator.getNUnique( operEx.args.length )
      List( PolyOperT( ts, OperT( TupT( ts : _* ), TupT( ts : _* ) ) ) )
    case TlaSetOper.times =>
      val ts = typeVarGenerator.getNUnique( operEx.args.length )
      List( PolyOperT( ts, OperT( TupT( ts map SetT : _* ), SetT( TupT( ts : _* ) ) ) ) )

    /** Control */
    case TlaControlOper.ifThenElse =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( BoolT, t, t ), t ) ) )
      // We forbid CASE without OTHER
//    case TlaControlOper.caseNoOther =>
//      val n = operEx.args.length / 2
//      val t = typeVarGenerator.getUnique
//      val tupArgs = for {
//        _ <- 1 to n
//        v <- List( BoolT, t )
//      } yield v
//      List( PolyOperT( List( t ), OperT( TupT( tupArgs : _* ), t ) ) )
    case TlaControlOper.caseWithOther =>
      val n = ( operEx.args.length - 1 ) / 2
      val t = typeVarGenerator.getUnique
      val tupArgs = for {
        _ <- 1 to n
        v <- List( BoolT, t )
      } yield v

      List( PolyOperT( List( t ), OperT( TupT( t +: tupArgs : _* ), t ) ) )

    /** Oper */
    case TlaOper.apply =>
      val n = operEx.args.length - 1
      val t = typeVarGenerator.getUnique
      if ( n == 0 ) {
        List( PolyOperT( List( t ), OperT( TupT( t ), t ) ) )
      }
      else {
        val ts = typeVarGenerator.getNUnique( n )
        List( PolyOperT( t +: ts, OperT( TupT( OperT( TupT( ts : _* ), t ) +: ts : _* ), t ) ) )
      }

    /** Sequences */
    case TlaSeqOper.concat =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ), SeqT( t ) ), SeqT( t ) ) ) )
    case TlaSeqOper.head =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ) ), t ) ) )
    case TlaSeqOper.tail =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ) ), SeqT( t ) ) ) )
    case TlaSeqOper.len =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ) ), IntT ) ) )
    case TlaSetOper.seqSet =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SetT( t ) ), SetT( SeqT( t ) ) ) ) )
    case TlaSeqOper.append =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ), t ), SeqT( t ) ) ) )
    case TlaSeqOper.subseq =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ), IntT, IntT ), SeqT( t ) ) ) )
    case TlaSeqOper.selectseq =>
      val t = typeVarGenerator.getUnique
      List( PolyOperT( List( t ), OperT( TupT( SeqT( t ), OperT( TupT( t ), BoolT ) ), SeqT( t ) ) ) )

    /** Overloaded */
    case TlaFunOper.app =>
      // A function is always possible
      val funSig = {
        val ts = typeVarGenerator.getNUnique( 2 )
        val List( t1, t2 ) = ts
        PolyOperT( ts, OperT( TupT( FunT( t1, t2 ), t1 ), t2 ) )
      }

      // def not val, because there's no need to evaluate it in the case of records
      def seqSig : PolyOperT = {
        val t = typeVarGenerator.getUnique
        PolyOperT( List( t ), OperT( TupT( SeqT( t ), IntT ), t ) )
      }

      // For tuples/records we need integer, resp. string, constants
      val Seq( _, arg ) = operEx.args
      arg match {
        case ValEx( TlaInt( i ) ) =>
          val sparseTupSig = {
            val t = typeVarGenerator.getUnique
            PolyOperT( List( t ), OperT( TupT( SparseTupT( Map( i.toInt -> t ) ), IntT ), t ) )
          }
          List( funSig, seqSig, sparseTupSig )
        case ValEx( TlaStr( s ) ) =>
          val recSig = {
            val t = typeVarGenerator.getUnique
            PolyOperT( List( t ), OperT( TupT( RecT( Map( s -> t ) ), IntT ), t ) )
          }
          List( funSig, recSig )
        case _ => List( funSig, seqSig )
      }

    case TlaFunOper.except =>
      val n = ( operEx.args.length - 1 ) / 2
      val allTupArgs = operEx.args.zipWithIndex collect {
        case (OperEx( TlaFunOper.tuple, tupArgs@_* ), i) if i % 2 == 1 =>
          tupArgs
      }
      val tupSizes = ( allTupArgs map {
        _.length
      } ).toSet
      assert( tupSizes.size == 1 )
      // All of the arguments are k-tuples
      val k = tupSizes.head

      val funSig = {
        val t = typeVarGenerator.getUnique
        val ts = typeVarGenerator.getNUnique( k )
        val fnChain = ts.foldRight[TlaType]( t ) { case (from, to) => FunT( from, to ) }
        val allPairs = for {
          _ <- 1 to n
          v <- List( TupT( ts : _* ), t )
        } yield v
        PolyOperT( t +: ts, OperT( TupT( fnChain +: allPairs : _* ), fnChain ) )
      }

      val recCandidate = allTupArgs forall { s =>
        s forall {
          case ValEx( _ : TlaStr ) => true
          case _ => false
        }
      }

      val recSigOpt =
        if ( !recCandidate ) None
        else {
          val ts = typeVarGenerator.getNUnique( n )
          val tups = operEx.args.zipWithIndex collect {
            case (OperEx( TlaFunOper.tuple, tupargs@_* ), i)
              if i % 2 == 1 && ( tupargs forall {
                case ValEx( _ : TlaStr ) => true
                case _ => false
              } ) =>
              tupargs map {
                _.asInstanceOf[ValEx].value.asInstanceOf[TlaStr].value
              }
          }

          def expandIteratedMap( leafVal : TlaType, strSeq : Seq[String], baseMap : TypeMap[String] ) : TypeMap[String] = strSeq match {
            case h +: Nil =>
              baseMap + ( h -> leafVal )
            case h +: t =>
              baseMap.getOrElse( h, RecT( Map.empty ) ) match {
                case RecT( recMap ) =>
                  baseMap + ( h -> RecT( expandIteratedMap( leafVal, t, recMap ) ) )
                case _ =>
                  throw new IllegalArgumentException( "Malformed nested record map" )
              }
          }

          val recT = ts.zip( tups ).foldLeft( RecT( Map.empty ) ) {
            case (RecT( recMap ), (t, strTup)) =>
              RecT( expandIteratedMap( t, strTup, recMap ) )
          }

          val allPairs = for {
            t <- ts
            v <- List( TupT( Seq.fill( k )( StrT ) : _* ), t )
          } yield v

          Some(
            PolyOperT( ts, OperT( TupT( recT +: allPairs : _* ), recT ) )
          )
        }

      List( funSig ) ++ recSigOpt

    case o => throw new IllegalArgumentException(
      s"Signature of operator ${o.name} is not known"
    )
  }
}

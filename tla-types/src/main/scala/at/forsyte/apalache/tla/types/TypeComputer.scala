package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.types.TypeComputer.Binding
import com.sun.istack.internal.Interned

import scalaz.State

object TypeComputer {
  type Binding = Map[String, TlaType]
  type Substitution = Map[Int, TlaType]

  sealed case class Internals(
                                       substitution : Substitution,
                                       assignments : TypeAssignment,
                                       knownOperators : Map[String, OperT]
                                     )

  type TCState[T] = State[Internals,T]
  type TypeReturnState = TCState[TlaType]
  type TypeReturnOptState = TCState[Option[TlaType]]

  class IncompatibleTypesException( arg: String, t1: TlaType, t2: TlaType ) extends
    Exception( s"Attempting to assign incompatible types [$t1] and [$t2] to $arg." )

  def applySubstitution( substitution: Substitution )( t : TlaType ) : TlaType = {
    val self = applySubstitution(substitution)(_)
    t match {
      case TypeVar( i ) => substitution.get( i ) map self getOrElse t
      case FunT( d, c ) => FunT( self( d ), self( c ) )
      case OperT( TupT( args@_* ), c ) => OperT( TupT( args map self : _* ), self( c ) )
      case SetT( s ) => SetT( self( s ) )
      case SeqT( s ) => SeqT( self( s ) )
      case TupT( ts@_* ) => TupT( ts map self : _* )
      case SparseTupT( tmap ) => SparseTupT( tmap map { case (k, v) => k -> self( v ) } )
      case RecT( tmap ) => RecT( tmap map { case (k, v) => k -> self( v ) } )
      case PolyOperT( ts, OperT( TupT( args@_* ), retT ) ) =>
        PolyOperT( ts, OperT( TupT( args map self : _* ), self( retT ) ) )
      case x => x
    }
  }


}

/**
  * Assumptions:
  *   - All variables (bound or free), operators and parameters have unique names.
  */

class TypeComputer(
                    bodyMap: BodyMap,
                    globalBinding: Binding // variables, constants
                  ) {
  import TypeComputer._

  private val tvg = new TypeVarGenerator
  private val sigGen = new SignatureGenerator( tvg )



  private var knownOperators : Map[String, OperT] = Map.empty

  private var asgn: TypeAssignment = Map.empty
  private val unifier = new TypeUnifier

  def mkParamType( fp: FormalParam ) : TlaType = fp match {
    case SimpleFormalParam(_) => tvg.getUnique
    case OperFormalParam( _, n ) => OperT( TupT( tvg.getNUnique( n ) :_*), tvg.getUnique )
  }

//  def attemptUpdateVar(
//                        varName: String,
//                        newType: TlaType,
//                        substitution: Substitution
//                      ) : UnificationResult =
//    globalBinding.get( varName ) match {
//      case None =>
//        throw new Exception("Binding should never be undefined for variables.")
//      case Some( oldType ) =>
//        // Unify with newType, if possible
//        // The first call is expected to unify a type variable and a concrete type
//        unifier.unify( oldType, newType ) flatMap {
//          case UnificationResult( unifiedType, sub ) =>
//            // The substitution must be compatible (a variable can't be assigned 2 conflicting types at once)
//            unifier.disjointMapMerge( variableSubstitution, sub ) map {
//              s => UnificationResult( unifiedType, s )
//            }
//        } getOrElse {
//          throw new IncompatibleTypesException( varName, oldType, newType )
//        }
////        } match {
////          case Some( UnificationResult( unifiedType, sub ) ) =>
////            variableSubstitution = sub // extend the substitution
////            globalBinding += varName -> unifiedType // update the global binding too
////            unifiedType
////          case None =>
////            throw new IncompatibleTypesException(
////              varName,
////              oldType, // unifier.sub( oldType ),
////              newType // unifier.sub( newType )
////            )
////        }
//    }

//  def attemptUpdateUID_S(
//                          uid : UID,
//                          newType : TlaType
//                        ) : TypeReturnOptState = {
//    case internals@Internals( substitution, assignments, _ ) =>
//      assignments.get( uid ) match {
//        case None =>
//          // If the UID has not been assigned a type yet we can freely assign it newType
//          val tp = applySubstitution( substitution )( newType )
//          ( internals.copy( assignments = assignments + (uid -> tp) ), Option(tp) )
//        case Some( oldType ) =>
//          // Otherwise, we attempt unification ...
//          unifier.unify( oldType, newType ) flatMap {
//            case UnificationResult( unifiedType, sub ) =>
//              // ... which must respect existing variable assignments, if they exist
//              unifier.disjointMapMerge( substitution, sub ) map { newSub =>
//                asgn += uid -> unifiedType
//                (internals.copy(
//                  assignments = assignments + ( uid -> unifiedType ),
//                  substitution = newSub
//                ), Option(unifiedType))
//              }
//          } getOrElse {
//            (internals, Option.empty[TlaType])
//          }
//      }
//  }

  def attemptUpdateUID(
                        uid: UID,
                        newType: TlaType,
                        substitution: Substitution
                      ) : UnificationResult = asgn.get( uid ) match {
      case None =>
        // If the UID has not been assigned a type yet we can freely assign it newType
        val tp = applySubstitution( substitution )( newType )
        asgn += uid -> tp
        UnificationResult( tp, substitution )
      case Some( oldType ) =>
        // Otherwise, we attempt unification ...
        unifier.unify( oldType, newType ) flatMap {
          case UnificationResult( unifiedType, sub ) =>
            // ... which must respect existing variable assignments, if they exist
            unifier.disjointMapMerge( substitution, sub ) map { newSub =>
              asgn += uid -> unifiedType
              UnificationResult( unifiedType, newSub )
            }
        } getOrElse {
          throw new IncompatibleTypesException( s"UID(${uid.id})", oldType, newType )
        }


//        } match {
//          case Some( UnificationResult( unifiedType, sub ) ) =>
//            variableSubstitution = sub
//            // If unification succeeds, we can assign the unified type
//            asgn += uid -> unifiedType
//            unifiedType
//          case None =>
//            throw new IncompatibleTypesException(
//              s"UID(${uid.id})",
//              oldType, // unifier.sub( oldType ),
//              newType // unifier.sub( newType )
//            )
//        }
  }

  def literalType( v: TlaValue ) : TlaType =
    v match {
      case _: TlaInt => IntT
      case TlaIntSet => SetT( IntT )
      case TlaNatSet => SetT( IntT )
      case _: TlaStr => StrT
      case TlaStrSet => SetT( StrT )
      case _: TlaBool => BoolT
      case TlaBoolSet => SetT( BoolT )
    }

//  def resolveOperatorApplication_S(
//                                  retExId: UID,
//                                  operNameExId: UID,
//                                  operT : OperT,
//                                  args: Seq[TlaEx],
//                                ) : TypeReturnOptState = operT match {
//    case OperT( TupT( tupArgs@_* ), retT ) =>
//      assert( tupArgs.length == args.length )
//      val finalSub = tupArgs.zip( args ).foldLeft( substitution ) {
//        case (partialSub, (sigArgT, arg)) =>
//          val UnificationResult( computedT, newSub ) = buildTypeAssignment( partialSub, arg )
//          // Attempt to update with both the computed and the signature-required types
//          // They should unify
//          attemptUpdateUID( arg.ID, sigArgT, newSub ).substitution
//      }
//      val UnificationResult( _, subAfterOperUpdate ) = attemptUpdateUID( operNameExId, operT, finalSub )
//      val UnificationResult( finalT, _ ) = attemptUpdateUID( retExId, retT, subAfterOperUpdate )
//      // we discard the computed substitution, because it substitutes operator parameters
//      UnificationResult( finalT, substitution )
//  }

  def resolveOperatorApplication(
                                  retExId: UID,
                                  operNameExId: UID,
                                  operT : OperT,
                                  args: Seq[TlaEx],
                                  substitution: Substitution
                                ) : UnificationResult = operT match {
    case OperT( TupT( tupArgs@_* ), retT ) =>
      assert( tupArgs.length == args.length )
      val finalSub = tupArgs.zip( args ).foldLeft( substitution ) {
        case ( partialSub, (sigArgT, arg) ) =>
          val UnificationResult(computedT, newSub) = buildTypeAssignment( partialSub, arg )
          // Attempt to update with both the computed and the signature-required types
          // They should unify
          attemptUpdateUID( arg.ID, sigArgT, newSub ).substitution
      }
      val UnificationResult( _, subAfterOperUpdate ) = attemptUpdateUID( operNameExId, operT, finalSub )
      val UnificationResult( finalT, _ ) = attemptUpdateUID( retExId, retT, subAfterOperUpdate )
      // we discard the computed substitution, because it substitutes operator parameters
      UnificationResult( finalT, substitution )
  }

//  def resolveApply_S( ex : OperEx ) : TypeReturnOptState = {
//    case internals@Internals( _, _, knownOpers ) => ex match {
//      case OperEx( TlaOper.apply, nameEx@NameEx( opName ), args@_* ) =>
//        // If the operator name has an entry in the globalBinding,
//        // it is an operator parameter
//        globalBinding.get( opName ) match {
//          case Some( operParamT : OperT ) =>
//            resolveOperatorApplication_S( ex.ID, nameEx.ID, operParamT, args )
//          case None => for {
//            operTOpt <- knownOpers.get( opName ) map { t =>
//              State[Internals, Option[TlaType]] {
//                _ => (internals, Option( t ))
//              }
//            } getOrElse {
//              // if it's not yet known, we compute it here, once
//              val (fParams, body) = bodyMap( opName )
//              for {
//                rOpt <- buildTypeAssignment_S( body ) map {
//                  _ map { typeOfBody =>
//                    OperT( TupT( fParams map { p => globalBinding( p.name ) } : _* ), typeOfBody )
//                  }
//                }
//              } yield rOpt match {
//                case Some( r ) =>
//                  (internals.copy( knownOperators = knownOpers + ( opName -> r ) ), rOpt)
//                case None =>
//                  (internals, rOpt)
//              }
//            }
//            resolvedOpApOpt <- operTOpt match {
//              case Some( operT: OperT ) =>
//                resolveOperatorApplication_S( ex.ID, nameEx.ID, operT, args )
//              case _ => State[Internals, Option[TlaType]]{ s => (s, None) }
//            }
//          } yield resolvedOpApOpt
//          case _ => State[Internals, Option[TlaType]]{ s => (s, None) }
////            throw new Exception( s"Operator parameters should have operator types, found: $opType" )
//        }
//    }
//  }

//  def buildTypeAssignment_S(
//                             ex : TlaEx
//                           ) : TypeReturnOptState = {
//    case internals@Internals( substitution, assignments, knownOpers ) =>
//      ex match {
//        case ValEx( v ) =>
//          attemptUpdateUID_S( ex.ID, literalType( v ) )
//        case NameEx( n ) =>
//          attemptUpdateUID_S( ex.ID, globalBinding( n ) )
//        case OperEx( TlaActionOper.prime, NameEx( n ) ) =>
//          val prime2String = s"$n'"
//          attemptUpdateUID_S( ex.ID, globalBinding( prime2String ) )
//        case opEx@OperEx( TlaOper.apply, _* ) =>
//          resolveApply_S( opEx )
//        case opEx@OperEx( oper, args@_* ) =>
//          val sigs = sigGen.getPossibleSignatures( opEx )
//          assert( sigs.nonEmpty )
//          val (candidates, finalSub) = sigs.foldRight( (List.empty[TlaType], substitution) ) {
//            case (PolyOperT( _, OperT( TupT( tupArgs@_* ), retT ) ), (partialRetTList, partialSub)) =>
//              assert( tupArgs.length == args.length )
//              val newSub = tupArgs.zip( args ).foldLeft( partialSub ) {
//                case (pS, (sigArgT, arg)) =>
//                  val UnificationResult( _, newPartialSub ) = buildTypeAssignment( pS, arg )
//                  val UnificationResult( _, subAfterUpdate ) = attemptUpdateUID( arg.ID, sigArgT, newPartialSub )
//                  subAfterUpdate
//              }
//              (retT +: partialRetTList, newSub)
//          }
//          val thisType = candidates match {
//            case h +: Nil => h
//            case _ => AmbiguousType( candidates : _* )
//          }
//          attemptUpdateUID( ex.ID, thisType, finalSub )
//
//        case LetInEx( body, defs@_* ) =>
//          State[Internals, Option[TlaType]] { s => (s,None) }
//      }
//  }


  def buildTypeAssignment(
                           substitution: Substitution,
                           ex: TlaEx
                         ) : UnificationResult = ex match {
    case ValEx( v ) =>
      attemptUpdateUID( ex.ID, literalType( v ), substitution )
    case NameEx( n ) =>
      attemptUpdateUID( ex.ID, globalBinding( n ), substitution )
    case OperEx( TlaActionOper.prime, NameEx( n ) ) =>
      val prime2String = s"$n'"
      attemptUpdateUID( ex.ID, globalBinding( prime2String ), substitution )
    case OperEx( TlaOper.apply, nameEx@NameEx( opName ), args@_* ) =>
      // If the operator name has an entry in the globalBinding,
      // it is an operator parameter
      globalBinding.get( opName ) match {
        case Some( operParamT : OperT ) =>
          resolveOperatorApplication( ex.ID, nameEx.ID, operParamT, args, substitution )
        case None =>
          knownOperators.get( opName ) map {
            t => UnificationResult( t, substitution )
          } getOrElse {
            // if it's not yet known, we compute it here, once
            val TlaOperDecl( _, fParams, body ) = bodyMap( opName )
            val UnificationResult( typeOfBody, sub ) = buildTypeAssignment( substitution, body )
            val r = OperT( TupT( fParams map { p => globalBinding( p.name ) } : _* ), typeOfBody )
            knownOperators += opName -> r
            UnificationResult( r, sub )
          } match {
            case UnificationResult( operT : OperT, sub ) =>
              resolveOperatorApplication( ex.ID, nameEx.ID, operT, args, sub )
            case UnificationResult( t, _ ) =>
              throw new Exception( s"Operator parameters should have operator types, found: $t" )
          }
        case Some( opType ) =>
          throw new Exception( s"Operator parameters should have operator types, found: $opType" )
      }
    case opEx@OperEx( oper, args@_* ) =>
      val sigs = sigGen.getPossibleSignatures( opEx )
      assert( sigs.nonEmpty )
      val (candidates, finalSub) = sigs.foldRight( (List.empty[TlaType], substitution) ) {
        case (PolyOperT( _, OperT( TupT( tupArgs@_* ), retT ) ), (partialRetTList, partialSub)) =>
          assert( tupArgs.length == args.length )
          val newSub = tupArgs.zip( args ).foldLeft( partialSub ) {
            case (pS, (sigArgT, arg)) =>
              val UnificationResult( _, newPartialSub ) = buildTypeAssignment( pS, arg )
              val UnificationResult( _, subAfterUpdate ) = attemptUpdateUID( arg.ID, sigArgT, newPartialSub )
              subAfterUpdate
          }
          (retT +: partialRetTList, newSub)
      }

      //
      //          foreach {
      //            case (sigArgT, arg) =>
      //              val UnificationResult(computedArgT, newSub) = buildTypeAssignment( substitution, arg )
      //              // Attempt to update with both the computed and the signature-required types
      //              // They should unify
      //              attemptUpdateUID( arg.ID, computedArgT, newSub )
      //              attemptUpdateUID( arg.ID, sigArgT, newSub )
      //            // we discard newSub
      //          }
      //          retT
      val thisType = candidates match {
        case h +: Nil => h
        case _ => AmbiguousType( candidates : _* )
      }
      attemptUpdateUID( ex.ID, thisType, finalSub )

    case LetInEx( body, defs@_* ) =>
      UnificationResult( TypeVar( -1 ), substitution )
  }

  def getWithSubsitution(
                          substitution : Substitution
                        ) : (TypeAssignment, Binding, Map[String, TlaType]) = //(asgn, globalBinding)
    (
      asgn map {
        case (k, v) => k -> applySubstitution( substitution )( v )
      },
      globalBinding map {
        case (k, v) => k -> applySubstitution( substitution )( v )
      },
      knownOperators map {
        case (k, v) => k -> applySubstitution( substitution )( v )
      }
    )
}

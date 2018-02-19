package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import at.forsyte.apalache.tla.lir.values.TlaFalse

object SymbTransGenerator extends TypeAliases {

  private object helperFunctions {
    type LabelMapType = Map[UID, Set[UID]]
    type AssignmentSelections = Set[Set[UID]]
    type SelMapType = Map[UID , AssignmentSelections]

    def allCombinations[ValType]( p_sets: Seq[Set[Set[ValType]]]) : Set[Set[ValType]] = {
      if( p_sets.length == 1 )
        p_sets.head
      else {
        val one = p_sets.head
        val rest = allCombinations( p_sets.tail )

        (for {s <- one}
          yield rest.map( st => st ++ s )).fold( Set() )( _ ++ _ )
      }
    }

    def labelsAt( p_ex : TlaEx, p_partialSel : SelMapType ) : Set[UID] = labelsAt( p_ex.ID, p_partialSel )

    def labelsAt( p_id : UID, p_partialSel : SelMapType ) : Set[UID] = {
      p_partialSel.getOrElse( p_id, Set() ).fold( Set())( _ ++ _)
    }

    /**
      * Symbolic transitions are uniquely characterized by the intersections of branches with
      * an assignment strategy.
      * By computing all possibilities for such intersections, we effectively consider
      * all equivalence classes of ~_A.
      *
      * Since we know how to recursively compute branch sets, we can easily compute branch intersection sets
      */
    def makeAllSelections( p_phi : TlaEx, p_stratSet : Set[UID] ) : SelMapType = {
      val leafJudge : TlaEx => Boolean = AlphaTLApTools.isCand
      val defaultVal : AssignmentSelections = Set( Set() )
      val default : SelMapType = Map()
      def leafFun( p_ex : TlaEx ) : SelMapType =
        if ( p_stratSet.contains( p_ex.ID ) ) Map(p_ex.ID -> Set( Set( p_ex.ID ) ) ) else default
      def parentFun( p_ex: TlaEx, p_childResults: Seq[SelMapType]) : SelMapType = {
        p_ex match {
          case OperEx( oper, args@_* ) =>
            oper match {
              case TlaBoolOper.and =>
                /** Unify all child maps */
                val superMap = p_childResults.fold( Map() )( _ ++ _ )

                /** The set of all child labels */
                val mySet = allCombinations( args.map( x => superMap.getOrElse(x.ID, defaultVal ) ) )
                superMap + ( p_ex.ID -> mySet )

              case TlaBoolOper.or =>
                val superMap = p_childResults.fold( Map() )( _ ++ _ )
                val mySet = args.map( x => superMap.getOrElse(x.ID, defaultVal ) ).fold( Set() )( _ ++ _ )
                superMap + ( p_ex.ID -> mySet )

              case TlaBoolOper.exists =>
                val childMap = p_childResults.tail.tail.head
                childMap + ( p_ex.ID -> childMap.getOrElse(args.tail.tail.head.ID, defaultVal ) )
              case TlaControlOper.ifThenElse =>
                val superMap = p_childResults.tail.fold( Map() )( _ ++ _ )
                val mySet = args.tail.map( x => superMap.getOrElse(x.ID, defaultVal ) ).fold( Set() )( _ ++ _ )
                superMap + ( p_ex.ID -> mySet )
              case _ => default
            }
          case _ => default
        }
      }

      SpecHandler.bottomUpVal( p_phi, leafJudge,leafFun, parentFun, default )

    }

    def mkOrdered( p_asgnSet : Set[UID],
                   p_strat : StrategyType
                 ) : AssignmentType = {
      p_strat.filter( p_asgnSet.contains )
    }

    def assignmentFilter( p_ex : TlaEx,
                          p_selection : Set[UID],
                          p_allSelections : SelMapType
                        ) : TlaEx = {
      p_ex match {
        case OperEx( TlaBoolOper.or, args@_* ) =>
          /**
            * Or-branches have the property that they either contain
            * all assignments or none of them. Therefore it suffices to check for
            * non-emptiness of the intersection.
            */

          val newArgs = args.filter(
            x => labelsAt(x, p_allSelections).exists( y => p_selection.contains( y ) )
          )
          if ( newArgs.isEmpty )
            p_ex
          else {
            assert( newArgs.size == 1 )
            newArgs.head // if nonempty, it has exactly 1 member
          }
        case OperEx( TlaControlOper.ifThenElse, cond, args@_* ) =>
          val newArgs = args.map(
            x => if (labelsAt(x, p_allSelections).exists( y => p_selection.contains( y ) ))
              x else ValEx(TlaFalse)
          )
          OperEx( TlaControlOper.ifThenElse, cond +: newArgs:_* )

        case _ => p_ex
      }
    }


    def restrictToSelections( p_ex : TlaEx,
                              p_strat: StrategyType,
                              p_selections : SelMapType
                            ) : Seq[SymbTrans] = {

      p_selections( p_ex.ID ).map( s =>
        (
          mkOrdered( s, p_strat ),
          SpecHandler.getNewEx( p_ex, assignmentFilter( _, s, p_selections ) )
        )
      ).toSeq
    }

  }

  def apply( p_phi : TlaEx, p_asgnStrategy : StrategyType ) : Seq[SymbTrans] = {

    import helperFunctions._

    /** For certain purposes, we do not care about the order of assignments.
      * It is therefore helpful to have a set structure, with faster lookups. */
    val stratSet = p_asgnStrategy.toSet

    /** We make sure that the above requirement actually holds. */
    val selections = makeAllSelections(p_phi, stratSet)

    /** Sanity check, all selections are the same size */
    val allSizes = selections( p_phi.ID).map( _.size )
    assert(allSizes.size == 1 )

    restrictToSelections( p_phi, p_asgnStrategy, selections )

  }

}

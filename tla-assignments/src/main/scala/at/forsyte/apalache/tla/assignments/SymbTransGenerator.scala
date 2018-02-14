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

    def joinSetMaps[K, V]( p_map1 : Map[K, Set[V]],
                           p_map2 : Map[K, Set[V]]
                         ) : Map[K, Set[V]] = {
      Map[K, Set[V]](
        ( p_map1.keySet ++ p_map2.keySet ).toSeq.map(
          k => (k, p_map1.getOrElse( k, Set[V]() ) ++ p_map2.getOrElse( k, Set[V]() ))
        ) : _*
      )
    }

    /**
      * Shorthand for common .getOrElse uses
      */
    def labelsAt( p_ex : TlaEx,
                  p_knownLabels : LabelMapType
                ) : Set[UID] = p_knownLabels.getOrElse( p_ex.ID, Set() )

    /**
      * Decides whether a given [[at\.forsyte\.apalache\.tla\.lir\.TlaEx]] is considered a leaf in the formula tree.
      * For our puposes, leaves are assignment candidates, i.e. expressions of the
      * form x' \in S.
      * @param p_ex Any TLA expression
      * @return `true` iff the expression is a leaf in the formula tree.
      */
    def leafJudge( p_ex : TlaEx ) : Boolean = AlphaTLApTools.isCand( p_ex )

    /**
      * Creates a partial label map at a leaf.
      * @param p_ex Leaf expression.
      * @param p_stratSet The assignment strategy.
      * @return The empty map, if the leaf is not part of the strategy, otherwise the one-key
      *         map, which assigns to the leaf ID a singleton which contains that ID.
      */
    def leafFun( p_ex : TlaEx,
                 p_stratSet : Set[UID]
               ) : LabelMapType = {
      if ( p_stratSet.contains( p_ex.ID ) ) {
        Map( p_ex.ID -> Set( p_ex.ID ) )
      }
      else
        Map()
    }

    /**
      * Constructs a new label at the parent from child labels.
      * @param p_ex Current node in the formula tree.
      * @param p_childResults All the maps computed at child nodes.
      * @return A new label map, which agrees with all child maps and additionally assigns to the current
      *         node ID the union of all label sets found at its children.
      */
    def parentFun( p_ex : TlaEx,
                   p_childResults : Seq[LabelMapType]
                 ) : LabelMapType = {

      p_ex match {
        /** Guaranteed, if invoked by the [[SpecHandler]] */
        case OperEx( _, args@_* ) =>

          /** Unify all child maps */
          val superMap = p_childResults.fold( Map() )( joinSetMaps )

          /** The set of all child labels */
          val mySet = args.map( labelsAt( _, superMap ) ).fold( Set() )( _ ++ _ )
          superMap + ( p_ex.ID -> mySet )

        case _ => Map()
      }

    }

    def labelAll( p_ex : TlaEx,
                  p_stratSet : Set[UID]
                ) : LabelMapType = {
      SpecHandler.bottomUpVal[LabelMapType](
        p_ex,
        leafJudge,
        leafFun( _, p_stratSet ),
        parentFun,
        Map()
      )
    }

    /**
      * Checks whether a triplet of a formula, a strategy and a labeling is consistent.
      */
    def isConsistentLabeling( p_ex : TlaEx,
                              p_stratSet : Set[UID],
                              p_knownLabels : LabelMapType
                            ) : Boolean = {
      p_ex match {
        /** If inner node, own labels must exist and be equal to the union of the child labels */
        case OperEx( TlaBoolOper.and |
                     TlaBoolOper.or |
                     TlaBoolOper.exists |
                     TlaControlOper.ifThenElse,
        args@_* ) =>
          p_knownLabels.contains( p_ex.ID ) && p_knownLabels( p_ex.ID ) == args.map(
            x => p_knownLabels.getOrElse( x.ID, Set() )
          ).fold( Set() )( _ ++ _ )
        case _ =>
          /** If leaf and part of the strategy, the label set must be a singleton */
          if ( p_stratSet.contains( p_ex.ID ) )
            p_knownLabels.contains( p_ex.ID ) && p_knownLabels( p_ex.ID ) == Set( p_ex.ID )
          /** Otherwise, must be unlabeled */
          else
            p_knownLabels.getOrElse( p_ex.ID, Set() ).isEmpty
      }
    }

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

    /**
      * Symbolic transitions are uniquely characterized by the intersections of branches with
      * an assignment strategy.
      * By computing all possibilities for such intersections, we effectively consider
      * all equivalence classes of ~_A.
      *
      * Since we know how to recursively compute branch sets, we can easily compute branch intersection sets
      */
    def makeAllSelections( p_phi : TlaEx, p_stratSet : Set[UID] ) : Set[Set[UID]] = {
      val leafJudge : TlaEx => Boolean = AlphaTLApTools.isCand
      val default : Set[Set[UID]] = Set( Set() )
      def leafFun( p_ex : TlaEx ) : Set[Set[UID]] =
        if ( p_stratSet.contains( p_ex.ID ) ) Set( Set( p_ex.ID ) ) else default
      def parentFun( p_ex: TlaEx, p_childVals: Seq[Set[Set[UID]]]) : Set[Set[UID]] = {
        p_ex match {
          case OperEx( oper, _* ) =>
            oper match {
              case TlaBoolOper.and =>
                  allCombinations( p_childVals )
              case TlaBoolOper.or => p_childVals.fold( Set() )( _ ++ _ )
              case TlaBoolOper.exists => p_childVals.tail.tail.head
              case TlaControlOper.ifThenElse => p_childVals.tail.head ++ p_childVals.tail.tail.head
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
                          p_labels : LabelMapType
                        ) : TlaEx = {
      p_ex match {
        case OperEx( TlaBoolOper.or, args@_* ) =>
          /**
            * Or-branches have the property that they either contain
            * all assignments or none of them. Therefore it suffices to check for
            * non-emptiness of the intersection.
            */
          val newArgs = args.filter(
            x => p_labels.getOrElse( x.ID, Set() ).exists( y => p_selection.contains( y ) )
          )
          if ( newArgs.isEmpty )
            p_ex
          else {
            assert( newArgs.size == 1 )
            newArgs.head // if nonempty, it has exactly 1 member
          }
        case OperEx( TlaControlOper.ifThenElse, cond, args@_* ) =>
          val newArgs = args.map(
            x => if (p_labels.getOrElse( x.ID, Set() ).exists( y => p_selection.contains( y ) ))
              x else ValEx(TlaFalse)
          )
          OperEx( TlaControlOper.ifThenElse, cond +: newArgs:_* )

        case _ => p_ex
      }
    }


    def restrictToSelections( p_ex : TlaEx,
                              p_strat: StrategyType,
                              p_labels : LabelMapType,
                              p_selections : Set[Set[UID]]
                            ) : Seq[SymbTrans] = {

      p_selections.map( s =>
        (
          mkOrdered( s, p_strat ),
          SpecHandler.getNewEx( p_ex, assignmentFilter( _, s, p_labels ) )
        )
      ).toSeq
    }

  }

  def apply( p_phi : TlaEx, p_asgnStrategy : StrategyType ) : Seq[SymbTrans] = {

    // TODO
    // SINGLE PASS LABELS + SELECTIONS

    import helperFunctions._

    /** For certain purposes, we do not care about the order of assignments.
      * It is therefore helpful to have a set structure, with faster lookups. */
    val stratSet = p_asgnStrategy.toSet

    /** We mark every node in the formula with a set of labels.
      * A node n is marked with a set S iff all elements of S are assignment candidates, which
      * appear in subformulas of n
      *  */
    val labels = labelAll( p_phi, stratSet )

    /** We make sure that the above requirement actually holds. */
    assert( isConsistentLabeling( p_phi, stratSet, labels ) )

    /** We make sure that the above requirement actually holds. */
    val selections = makeAllSelections(p_phi, stratSet)

    /** Sanity check, all selections should have the same size */
    assert( selections.map( _.size ).size == 1 )

    restrictToSelections( p_phi, p_asgnStrategy, labels, selections )

  }

}

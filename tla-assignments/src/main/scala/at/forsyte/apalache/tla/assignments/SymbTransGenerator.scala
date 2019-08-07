package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaFalse

/**
  * Constructs symbolic transitions from an assignment strategy.
  */
class SymbTransGenerator extends TypeAliases {

  private[assignments] object helperFunctions {
    type LabelMapType = Map[UID, Set[UID]]
    type AssignmentSelections = Set[Set[UID]]
    type SelMapType = Map[UID, AssignmentSelections]

    def allCombinations[ValType]( p_sets : Seq[Set[Set[ValType]]] ) : Set[Set[ValType]] = {
      if ( p_sets.length == 1 )
        p_sets.head
      else {
        val one = p_sets.head
        val rest = allCombinations( p_sets.tail )

        ( for {s <- one}
          yield rest.map( st => st ++ s ) ).fold( Set.empty[Set[ValType]] )( _ ++ _ )
      }
    }

    def labelsAt( p_ex : TlaEx, p_partialSel : SelMapType ) : Set[UID] = labelsAt( p_ex.ID, p_partialSel )

    def labelsAt( p_id : UID, p_partialSel : SelMapType ) : Set[UID] = p_partialSel.getOrElse(
      p_id,
      Set.empty[Set[UID]]
    ).fold(
      Set.empty[UID]
    )(
      _ ++ _
    )

    /**
      * Symbolic transitions are uniquely characterized by the intersections of branches with
      * an assignment strategy.
      * By computing all possibilities for such intersections, we effectively consider
      * all equivalence classes of ~_A.
      *
      * makeAllSelections(phi, A)(psi) returns the set { S \cap A | S \in Branches(psi) }, i.e.
      * the representatives of Branches(psi) / ~_A, for psi \in Sub(phi)
      */
    def makeAllSelections( p_phi : TlaEx, p_stratSet : Set[UID] ) : SelMapType = {
      val leafJudge : TlaEx => Boolean = AlphaTLApTools.isCand
      val defaultVal : AssignmentSelections = Set( Set() )
      val default : SelMapType = Map()

      /** Nodes with labels in A have one branch and therefore one (nonempty) intersection wtih A */
      def leafFun( p_ex : TlaEx ) : SelMapType =
        if ( p_stratSet.contains( p_ex.ID ) ) Map( p_ex.ID -> Set( Set( p_ex.ID ) ) ) else default

      /**
        * Otherwise, we look at the branching Lemmas to determine how to compute branch sets for
        * parents from the branch sets of children
        **/
      def parentFun( p_ex : TlaEx, p_childResults : Traversable[SelMapType] ) : SelMapType = {
        p_ex match {
          case OperEx( oper, args@_* ) =>
            oper match {
              /**
                * Branches( /\ \phi_i ) = { Br_1 U ... U Br_s | \forall i . Br_i \in Branches(\phi_i) }
                * { S \cap A | S \in Branches( /\ phi_i ) } =
                * { (Br_1 U ... U Br_s) \cap A | \forall i . Br_i \in Branches(\phi_i) } =
                * { (Br_1 \cap A) U ... U (Br_s \cap A) | \forall i . Br_i \in Branches(\phi_i) } =
                * { B_1 U ... U B_n | \forall i . B_i \in { T \cap A | T \in Branches(\phi_i)} }
                */
              case TlaBoolOper.and =>

                /** Unify all child maps, keysets are disjoint by construction */
                val unifiedMaps = p_childResults.fold( Map() )( _ ++ _ )

                val childBranchSets = args.map( x => unifiedMaps.getOrElse( x.ID, defaultVal ) )

                /** The set as computed from the lemma */
                val mySet = allCombinations( childBranchSets )
                unifiedMaps + ( p_ex.ID -> mySet )

              /**
                * Branches( \/ \phi_i ) = U Branches(\phi_i)
                *  { S \cap A | S \in Branches( \/ \phi_i )} =
                *  { S \cap A | S \in U Branches(\phi_i)} =
                *  U { S \cap A | S \in Branches(\phi_i)}
                */
              case TlaBoolOper.or =>
                val unifiedMaps = p_childResults.fold( Map() )( _ ++ _ )

                val childBranchSets = args.map( x => unifiedMaps.getOrElse( x.ID, defaultVal ) )

                val mySet = childBranchSets.fold( Set() )( _ ++ _ )
                unifiedMaps + ( p_ex.ID -> mySet )

              /**
                * Branches( \E x \in S . \phi ) = Branches( \phi )
                * { S \cap A | S \in Branches( \E x \in S . \phi )} =
                * { S \cap A | S \in Branches( \phi )} =
                */
              case TlaBoolOper.exists =>
                val childMap = p_childResults.tail.tail.head
                childMap + ( p_ex.ID -> childMap.getOrElse( args.tail.tail.head.ID, defaultVal ) )

              /**
                * Branches( ITE(\phi_c, \phi_t, \phi_e) ) = Branches( \phi_t ) U Branches( \phi_e )
                * { S \cap A | S \in Branches( ITE(\phi_c, \phi_t, \phi_e) )} =
                * { S \cap A | S \in Branches( \phi_t ) U Branches( \phi_e ) } =
                * { S \cap A | S \in Branches( \phi_t ) } U { S \cap A | S \in Branches( \phi_e ) }
                */
              case TlaControlOper.ifThenElse =>
                val unifiedMaps = p_childResults.tail.fold( Map() )( _ ++ _ )

                val childBranchSets = args.tail.map( x => unifiedMaps.getOrElse( x.ID, defaultVal ) )

                val mySet = childBranchSets.fold( Set() )( _ ++ _ )
                unifiedMaps + ( p_ex.ID -> mySet )
              case _ => default
            }
          case _ => default
        }
      }

      /**
        * NOTE: Rethink this, since it's a direct port from using RecursiveProcessor
        */
      def getSelMap( ex : TlaEx ) : SelMapType = ex match {
        case e if leafJudge( e ) => leafFun( e )
        case e@OperEx( _, args@_* ) =>
          val chdRes = args map getSelMap
          parentFun( e, chdRes )
        case _ => default
      }

      getSelMap( p_phi )
    }

    /**
      * Orders a selection by \prec_A
      *
      * @param p_asgnSet A selection S \subseteq A
      * @param p_strat   An assignment strategy A.
      * @return A sequence of elements s_1, ..., s_|S| from S, such that
      *         s_1 \prec_A ... \prec_A s_|S|
      */
    def mkOrdered( p_asgnSet : Set[UID],
                   p_strat : StrategyType
                 ) : AssignmentType = {
      p_strat.filter( p_asgnSet.contains ) // p_strat is already ordered
    }

    /**
      * Produces a formula restriction, but simplified by TLA+ semantics.
      *
      * @param p_ex            Input formula
      * @param p_selection     An assignment selection.
      * @param p_allSelections The partial selction map.
      * @return
      */
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
            x =>

              /**
                * \E S \in p_allSelections( x ) . S \cap p_selection \ne \emptyset
                * <=>
                * \E S \in p_allSelections( x ) . \E y \in S . y \in p_selection
                * <=>
                * \E S \in p_allSelections( x ) . \E y \in p_selection . y \in S
                */
              p_allSelections.getOrElse(
                x.ID, Set()
              ).exists(
                sel => p_selection.exists(
                  y => sel.contains( y )
                )
              )
            //            x => labelsAt( x, p_allSelections ).exists( y => p_selection.contains( y ) )
          )

          /**
            * If no assignments lie below, take the largest subformula.
            * It is guaranteed to belong to the union of branches.
            */
          if ( newArgs.isEmpty )
            p_ex

          /** otherwise, take the one intersecting branch */
          else {
            assert( newArgs.size == 1 )
            //            if( newArgs.size != 1 )
            //              throw new AssignmentException( "Stategy intersects more than one branch, expected 1 or 0" )
            //            newArgs.head
            /** recurse, since disjunctions aren't always expanded */
            assignmentFilter( newArgs.head, p_selection, p_allSelections )
          }

        /** ITE behaves like disjunction, but instead of dropping subformulas we replace them
          * with False, since we cannot evaluate the IF-condition */
        /** Jure, 13.2.2019: This only applies if at least one branch has an assignment, otherwise keep all */
        case OperEx( TlaControlOper.ifThenElse, cond, args@_* ) =>
          val newArgs = args.map(
            x => if ( labelsAt( x, p_allSelections ).exists( y => p_selection.contains( y ) ) )
              x else ValEx( TlaFalse )
          )
          if ( newArgs.forall( _ == ValEx( TlaFalse ) ) )
            p_ex
          else
            OperEx( TlaControlOper.ifThenElse, cond +: newArgs : _* )

        case _ => p_ex
      }
    }

    /**
      * Gathers the ordered selections and their corresponding restricted formulas.
      *
      * @param p_ex         Input formula.
      * @param p_strat      Assignment strategy
      * @param p_selections Map of partial assignment selections.
      * @return A sequence of pairs of ordered assignment selections and their symbolic transitions.
      */
    def restrictToSelections( p_ex : TlaEx,
                              p_strat : StrategyType,
                              p_selections : SelMapType
                            ) : Seq[SymbTrans] = {
      def newBodyFrom( s : Set[UID], ex : TlaEx ) : TlaEx = ex match {
        case OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, _ ), _* ) =>
          assignmentFilter( ex, s, p_selections )

        case OperEx( op, args@_* ) =>
          val childVals = args map {
            newBodyFrom( s, _ )
          }
          // Make sure to avoid creating new UIDs if not absolutely needed, as filtering
          // is done on the basis of UIDs not syntax
          val same = childVals == args

          val newEx = if ( same ) ex else OperEx( op, childVals : _* )

          /**
            * Since our selections depend on UIDs, we need to update accordingly.
            * Each element childVars[i] is a transformation (pruning) of args[i], so
            * the p_selections entry copies over, because the branch intersections are preserved
            */
          val updatedSelections = if ( same ) p_selections else {
            val newChildMap : SelMapType = args.zip(childVals).map {
              case (x,y) => y.ID -> p_selections.getOrElse( x.ID, Set.empty )
            }.toMap
            (p_selections ++ newChildMap) + (newEx.ID -> p_selections.getOrElse(ex.ID, Set.empty))
          }
          assignmentFilter( newEx, s, updatedSelections )

        case _ => assignmentFilter( ex, s, p_selections )
      }

      p_selections( p_ex.ID ).map( s =>
        (
          mkOrdered( s, p_strat ),
          newBodyFrom( s, p_ex )
        )
      ).toSeq
    }
  }

  /**
    * Point of access method
    *
    * @param p_phi          TLA+ formula
    * @param p_asgnStrategy Assignment strategy A for `p_phi`.
    * @see [[AssignmentStrategyEncoder]]
    * @return A collection of symbolic transitions, as defined by the equivalence classes of ~,,A,,
    */
  def apply( p_phi : TlaEx, p_asgnStrategy : StrategyType ) : Seq[SymbTrans] = {

    import helperFunctions._

    /** For certain purposes, we do not care about the order of assignments.
      * It is therefore helpful to have a set structure, with faster lookups. */
    val stratSet = p_asgnStrategy.toSet

    /** We compute the set of all branch intersections with `p_asgnStrategy` */
    val selections = makeAllSelections( p_phi, stratSet )

    /** Sanity check, all selections are the same size */
    val allSizes = selections( p_phi.ID ).map( _.size )
    assert( allSizes.size == 1 )
    //    if( allSizes.size != 1 )
    //      throw new AssignmentException("Assignment selections of unequal size constructed")

    /** We restrict the formula to each equivalence class (defined by an assignment selection) */
    restrictToSelections( p_phi, p_asgnStrategy, selections )

  }

}

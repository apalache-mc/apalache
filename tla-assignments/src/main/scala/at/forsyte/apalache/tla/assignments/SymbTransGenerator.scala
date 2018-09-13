package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
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
      * Since we know how to recursively compute branch sets, we can easily compute branch intersection sets
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
      def parentFun( p_ex : TlaEx, p_childResults : Seq[SelMapType] ) : SelMapType = {
        p_ex match {
          case OperEx( oper, args@_* ) =>
            oper match {
              /**
                * Branches( /\ \phi_i ) = { Br_1 U ... U Br_s | \forall i . Br_i \in Branches(\phi_i) }
                */
              case TlaBoolOper.and =>

                /** Unify all child maps */
                val superMap = p_childResults.fold( Map() )( _ ++ _ )

                /** The set of all child labels */
                val mySet = allCombinations( args.map( x => superMap.getOrElse( x.ID, defaultVal ) ) )
                superMap + ( p_ex.ID -> mySet )

              /**
                * Branches( \/ \phi_i ) = U Branches(\phi_i)
                */
              case TlaBoolOper.or =>
                val superMap = p_childResults.fold( Map() )( _ ++ _ )
                val mySet = args.map( x => superMap.getOrElse( x.ID, defaultVal ) ).fold( Set() )( _ ++ _ )
                superMap + ( p_ex.ID -> mySet )

              /**
                * Branches( \E x \in S . \phi ) = Branches( \phi )
                */
              case TlaBoolOper.exists =>
                val childMap = p_childResults.tail.tail.head
                childMap + ( p_ex.ID -> childMap.getOrElse( args.tail.tail.head.ID, defaultVal ) )

              /**
                * Branches( ITE(\phi_c, \phi_t, \phi_e) ) = Branches( \phi_t ) U Branches( \phi_e )
                */
              case TlaControlOper.ifThenElse =>
                val superMap = p_childResults.tail.fold( Map() )( _ ++ _ )
                val mySet = args.tail.map( x => superMap.getOrElse( x.ID, defaultVal ) ).fold( Set() )( _ ++ _ )
                superMap + ( p_ex.ID -> mySet )
              case _ => default
            }
          case _ => default
        }
      }

      /**
        * Call bottomUpVal to propagate partial maps up the formula tree.
        * At the root, we obtain the set of all valid assignment selections, which is
        * in a one-to-one correspondence with the quotient set Branches(\phi) / ~_A
        **/
      SpecHandler.bottomUpVal( p_phi, leafJudge, leafFun, parentFun, default )

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
      p_strat.filter( p_asgnSet.contains )
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

          /** otherwise, take the one intersecting branch*/
          else {
            assert( newArgs.size == 1 )
//            if( newArgs.size != 1 )
//              throw new AssignmentException( "Stategy intersects more than one branch, expected 1 or 0" )
//            newArgs.head
            /** recurse, since disjunctions aren't always expanded */
            assignmentFilter( newArgs.head, p_selection, p_allSelections)
          }

        /** ITE behaves like disjunction, but instead of dropping subformulas we replace them
          * with False, since we cannot evaluate the IF-condition */
        case OperEx( TlaControlOper.ifThenElse, cond, args@_* ) =>
          val newArgs = args.map(
            x => if ( labelsAt( x, p_allSelections ).exists( y => p_selection.contains( y ) ) )
              x else ValEx( TlaFalse )
          )
          OperEx( TlaControlOper.ifThenElse, cond +: newArgs : _* )

        case _ => p_ex
      }
    }

    /**
      * Gathers the ordered selections and their corresponding restricted formulas.
      * @param p_ex Input formula.
      * @param p_strat Assignment strategy
      * @param p_selections Map of partial assignment selections.
      * @return A sequence of pairs of ordered assignment selections and their symbolic transitions.
      */
    def restrictToSelections( p_ex : TlaEx,
                              p_strat : StrategyType,
                              p_selections : SelMapType
                            ) : Seq[SymbTrans] = {

      def asgnCheck( ex : TlaEx) : Boolean = ex match {
        case OperEx( TlaSetOper.in, OperEx(TlaActionOper.prime, _), _*) => true
        case _ => false
      }

      p_selections( p_ex.ID ).map( s =>
        (
          mkOrdered( s, p_strat ),
          SpecHandler.recursiveTransform( p_ex, asgnCheck ,assignmentFilter( _, s, p_selections ) )
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

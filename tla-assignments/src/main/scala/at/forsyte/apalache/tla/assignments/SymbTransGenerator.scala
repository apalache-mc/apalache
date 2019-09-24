package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaFalse

/**
  * Constructs symbolic transitions from an assignment strategy.
  */
class SymbTransGenerator( tracker : TransformationTracker ) extends TypeAliases {

  private[assignments] object helperFunctions {
    type LabelMapType = Map[UID, Set[UID]]
    type AssignmentSelections = Set[Set[UID]]
    type SelMapType = Map[UID, AssignmentSelections]
    type letInMapType = Map[String, (UID,SelMapType)]

    def allCombinations[ValType]( p_sets : Seq[Set[Set[ValType]]] ) : Set[Set[ValType]] = {
      if ( p_sets.isEmpty )
        Set.empty[Set[ValType]]
      else if ( p_sets.length == 1 )
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

    /** Given an assignment strategy A and a TLA+ expression \phi, computes
      * { B \cap A | B \in Branches( \psi ) }
      * for all expresisons \psi \in Sub(\phi)
      *
      * @param ex Top-level expression
      * @param stratSet Assignment strategy
      * @param letInMap Auxiliary map, storing the already-computed branch-information for nullary LET-IN
      *                 defined operators.
      * @return A mapping of the form [e.ID |-> { B \cap A | B \in Branches( e ) } | e \in Sub(ex)]
      */
    def allSelections( ex : TlaEx, stratSet: Set[UID], letInMap: letInMapType = Map.empty ) : SelMapType = ex match {
      case e if AlphaTLApTools.isCand(e) =>
        if ( stratSet.contains( e.ID ) ) Map( e.ID -> Set( Set( e.ID ) ) ) else Map.empty[UID, AssignmentSelections]
      /**
        * Branches( /\ \phi_i ) = { Br_1 U ... U Br_s | \forall i . Br_i \in Branches(\phi_i) }
        * { S \cap A | S \in Branches( /\ phi_i ) } =
        * { (Br_1 U ... U Br_s) \cap A | \forall i . Br_i \in Branches(\phi_i) } =
        * { (Br_1 \cap A) U ... U (Br_s \cap A) | \forall i . Br_i \in Branches(\phi_i) } =
        * { B_1 U ... U B_n | \forall i . B_i \in { T \cap A | T \in Branches(\phi_i)} }
        */
      case OperEx(TlaBoolOper.and, args@_*) =>
        /** Unify all child maps, keysets are disjoint by construction */
        val unifiedMap = (args map { allSelections( _, stratSet, letInMap ) }).fold( Map.empty[UID, AssignmentSelections] ) { _ ++ _ }

        val childBranchSets = args.flatMap( x => unifiedMap.get( x.ID ) )

        /** The set as computed from the lemma */
        val mySet = allCombinations( childBranchSets )
        if ( mySet.isEmpty || mySet.exists( _.isEmpty) ) unifiedMap else unifiedMap + ( ex.ID -> mySet )

      /**
        * Branches( \/ \phi_i ) = U Branches(\phi_i)
        * { S \cap A | S \in Branches( \/ \phi_i )} =
        * { S \cap A | S \in U Branches(\phi_i)} =
        * U { S \cap A | S \in Branches(\phi_i)}
        */
      case OperEx(TlaBoolOper.or, args@_*)  =>
        val unifiedMap = (args map { allSelections( _, stratSet, letInMap ) }).fold( Map.empty[UID, AssignmentSelections]) { _ ++ _ }

        val childBranchSets = args.flatMap( x => unifiedMap.get( x.ID ) )

        val mySet = childBranchSets.fold( Set.empty[Set[UID]] )( _ ++ _ )
        if ( mySet.isEmpty || mySet.exists( _.isEmpty) ) unifiedMap else unifiedMap + ( ex.ID -> mySet )

      /**
        * Branches( \E x \in S . \phi ) = Branches( \phi )
        * { S \cap A | S \in Branches( \E x \in S . \phi )} =
        * { S \cap A | S \in Branches( \phi )} =
        */
      case OperEx(TlaBoolOper.exists, _, _, phi) =>
        val childMap = allSelections( phi, stratSet, letInMap )
        val mySet = childMap.getOrElse( phi.ID, Set( Set.empty[UID] ) )
        if ( mySet.exists( _.isEmpty) ) childMap else childMap + ( ex.ID -> mySet )

      /**
        * Branches( ITE(\phi_c, \phi_t, \phi_e) ) = Branches( \phi_t ) U Branches( \phi_e )
        * { S \cap A | S \in Branches( ITE(\phi_c, \phi_t, \phi_e) )} =
        * { S \cap A | S \in Branches( \phi_t ) U Branches( \phi_e ) } =
        * { S \cap A | S \in Branches( \phi_t ) } U { S \cap A | S \in Branches( \phi_e ) }
        */
      case OperEx(TlaControlOper.ifThenElse, _, thenAndElse@_*) =>
        val unifiedMap = (thenAndElse map { allSelections( _, stratSet, letInMap ) }).fold( Map.empty[UID, AssignmentSelections] ) { _ ++ _ }

        val childBranchSets = thenAndElse.flatMap( x => unifiedMap.get( x.ID ) )

        val mySet = childBranchSets.fold( Set.empty[Set[UID]] )( _ ++ _ )
        if ( mySet.isEmpty || mySet.exists( _.isEmpty) ) unifiedMap else unifiedMap + ( ex.ID -> mySet )

      case LetInEx( body, defs@_* ) =>
        val defMap = (defs map { d =>
          d.name -> (d.body.ID, allSelections(d.body, stratSet, letInMap))
        }).toMap
        val childMap = allSelections( body, stratSet, letInMap ++ defMap )
        val mySet = childMap.getOrElse( body.ID, Set( Set.empty[UID] ) )
        if ( mySet.exists( _.isEmpty) ) childMap else childMap + ( ex.ID -> mySet )

      // Nullary apply
      case OperEx(TlaOper.apply, NameEx(operName)) =>
        // Apply may appear in higher order operators, so it might not be possible to pre-analyze
        letInMap.get( operName ) match {
          case Some( (uid, lim) ) =>
            val mySet = lim.getOrElse( uid, Set( Set.empty[UID] ) )
            if ( mySet.exists( _.isEmpty) ) lim else lim + ( ex.ID -> mySet )
          case None => Map.empty[UID, AssignmentSelections]
        }

      case _ => Map.empty[UID, AssignmentSelections]
    }


    def sliceWith( selection : Set[UID], allSelections: SelMapType ) : TlaExTransformation = tracker.track {
      // Assignments are a base case, don't recurse on args
      case ex@OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, _ ), _* ) =>
        ex

      case ex@OperEx( TlaBoolOper.or, args@_* ) =>
        /**
          * Or-branches have the property that they either contain
          * all assignments or none of them. Therefore it suffices to check for
          * non-emptiness of the intersection.
          */
        /**
          * Jure, 16.9.19: This is no longer true, with the inclusion of LET-IN, as assignments that
          * happen within a LET-IN operator body can appear to belong to multiple branches.
          * */

        val newArgs = args.filter { x =>
          /**
            * \E S \in allSelections( x ) . S \cap selection \ne \emptyset
            * <=>
            * \E S \in allSelections( x ) . \E y \in S . y \in selection
            * <=>
            * \E S \in allSelections( x ) . \E y \in selection . y \in S
            * <=>
            * \E y \in selection . y \in \bigcup allSelections( x )
            */
          labelsAt( x, allSelections ) exists { selection.contains }
        }

//        /**
//          * If no assignments lie below, take the largest subformula.
//          * It is guaranteed to belong to the union of branches.
//          * Otherwise, take the one intersecting branch (recurse, since disjunctions aren't always expanded)
//          */
//        assert( newArgs.size < 2 )

//        newArgs.headOption.map( sliceWith( selection, allSelections) ).getOrElse( ex )
        newArgs match {
          case Nil => ex
          case head +: Nil => sliceWith( selection, allSelections)(head)
          case _ => OperEx( TlaBoolOper.or, newArgs map sliceWith( selection, allSelections) : _* )
        }

      /** We replace ITE(a,b,c) with either a /\ b or ~a /\ c, depending
        * on which branch has the assignment.
        * This only applies if exactly branch has an assignment, otherwise keep all */
      case ex@OperEx( TlaControlOper.ifThenElse, ifEx, args@_* ) =>
        val newTail = args.map(
          x => if ( labelsAt( x, allSelections ) exists {
            selection.contains
          } )
            sliceWith( selection, allSelections )( x ) else ValEx( TlaFalse )
        )

        newTail match {
          case ValEx( TlaFalse ) +: ValEx( TlaFalse ) +: Nil =>
            ex
          case newThen +: ValEx( TlaFalse ) +: Nil =>
            OperEx( TlaBoolOper.and, ifEx, newThen )
          case ValEx( TlaFalse ) +: newElse +: Nil =>
            OperEx( TlaBoolOper.and, OperEx( TlaBoolOper.not, ifEx ), newElse )
          case _ =>
            // Possible, because of LET-IN
            OperEx( TlaControlOper.ifThenElse, ifEx +: newTail : _* )
        }

      case ex@OperEx( op, args@_* ) =>
        val childVals = args map {
          sliceWith( selection, allSelections )
        }
        // Make sure to avoid creating new UIDs if not absolutely needed, as filtering
        // is done on the basis of UIDs not syntax
        if ( childVals == args ) ex else OperEx( op, childVals : _* )

      case ex@LetInEx( body, defs@_* ) =>
        val slice = sliceWith( selection, allSelections )
        val newDefs = defs map { d =>
          d.copy( body = slice( d.body ) )
        } // filterNot { _.body == ValEx( TlaFalse ) } ?

        val newBody = slice( body )

        val same = newDefs == defs && newBody == body

        if ( same ) ex
        else if ( newBody == ValEx( TlaFalse ) ) newBody
        else LetInEx( newBody, newDefs : _* )

      case ex => ex
    }

    /**
      * Orders a selection by \prec_A
      *
      * @param selection A selection S \subseteq A
      * @param strategy  An assignment strategy A.
      * @return A sequence of elements s_1, ..., s_|S| from S, such that
      *         s_1 \prec_A ... \prec_A s_|S|
      */
    def mkOrdered(
                   selection : Set[UID],
                   strategy : StrategyType
                 ) : AssignmentType = {
      strategy.filter( selection.contains ) // strategy is already ordered
    }

    /**
      * Gathers the ordered selections and their corresponding restricted formulas.
      *
      * @param ex         Input formula.
      * @param strategy      Assignment strategy
      * @param selections Map of partial assignment selections.
      * @return A sequence of pairs of ordered assignment selections and their symbolic transitions.
      */
    def getTransitions(
                        ex : TlaEx,
                        strategy : StrategyType,
                        selections : SelMapType
                      ) : Seq[SymbTrans] =
      selections( ex.ID ).map( s =>
        (
          mkOrdered( s, strategy ),
          sliceWith( s, selections )( ex )
        )
      ).toSeq
    }

  /**
    * Point of access method
    *
    * @param phi          TLA+ formula
    * @param asgnStrategy Assignment strategy A for `p_phi`.
    * @see [[AssignmentStrategyEncoder]]
    * @return A collection of symbolic transitions, as defined by the equivalence classes of ~,,A,,
    */
  def apply( phi : TlaEx, asgnStrategy : StrategyType ) : Seq[SymbTrans] = {

    import helperFunctions._

    /** For certain purposes, we do not care about the order of assignments.
      * It is therefore helpful to have a set structure, with faster lookups. */
    val stratSet = asgnStrategy.toSet

    /** We compute the set of all branch intersections with `asgnStrategy` */
    val selections = allSelections( phi, stratSet, Map.empty )

    /** Sanity check, all selections are the same size */
    val allSizes = selections( phi.ID ).map( _.size )
    assert( allSizes.size == 1 )

    /** We restrict the formula to each equivalence class (defined by an assignment selection) */
    getTransitions( phi, asgnStrategy, selections )
  }

}

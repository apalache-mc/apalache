package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{BoolT1, _}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaBool

import scala.collection.immutable.{SortedMap, SortedSet}

/**
 * Constructs symbolic transitions from an assignment strategy.
 * In the intermediate computations, we use sets of assignment selections to avoid sorting overhead.
 * The final result is sorted to produce deterministic results.
 */
class SymbTransGenerator(tracker: TransformationTracker) {

  private[assignments] object helperFunctions {
    // assignment selections as used in the intermediate computations, to avoid sorting overhead
    type AssignmentSelections = Set[SortedSet[UID]]
    // sorted assignment selections for the final output, to produce deterministic results
    type SortedAssignmentSelections = SortedSet[SortedSet[UID]]
    // assignment selections assigned to operator definitions, unsorted
    type SelMapType = SortedMap[UID, AssignmentSelections]
    // assignment selections assigned to operator definitions, sorted
    type SortedSelMapType = SortedMap[UID, SortedAssignmentSelections]
    // assignment selections assigned to LET-IN defined operators, unsorted
    type LetInMapType = SortedMap[String, (UID, SelMapType)]

    def allCombinations(p_sets: Seq[AssignmentSelections]): AssignmentSelections = {
      if (p_sets.isEmpty)
        Set.empty[SortedSet[UID]]
      else if (p_sets.length == 1)
        p_sets.head
      else {
        val head: AssignmentSelections = p_sets.head
        val tail: AssignmentSelections = allCombinations(p_sets.tail)

        // extend every assignment selection in tail with every assignment selection in head
        val extended = for { s <- head } yield tail.map(st => st ++ s)
        // now, flatten the extended sets
        extended.fold(Set.empty[SortedSet[UID]])(_ ++ _)
      }
    }

    def labelsAt(p_ex: TlaEx, p_partialSel: SelMapType): Set[UID] = labelsAt(p_ex.ID, p_partialSel)

    def labelsAt(p_id: UID, p_partialSel: SelMapType): Set[UID] = p_partialSel
      .getOrElse(
          p_id,
          Set.empty[Set[UID]],
      )
      .fold(
          Set.empty[UID]
      )(
          _ ++ _
      )

    /**
     * Given an assignment strategy A and a TLA+ expression \phi, computes { B \cap A | B \in Branches( \psi ) } for all
     * expresisons \psi \in Sub(\phi)
     *
     * @param ex
     *   Top-level expression
     * @param letInMap
     *   Auxiliary map, storing the already-computed branch-information for nullary LET-IN defined operators.
     * @return
     *   A mapping of the form [e.ID |-> { B \cap A | B \in Branches( e ) } | e \in Sub(ex)]
     */
    def allSelections(ex: TlaEx, letInMap: LetInMapType = SortedMap.empty): SelMapType = ex match {

      /** Base case, assignments */
      case e @ OperEx(ApalacheOper.assign, _, _) =>
        SortedMap(e.ID -> Set(SortedSet(e.ID)))

      /** Propagate into label bodies */
      case OperEx(TlaOper.label, body, _*) =>
        val bodyMap = allSelections(body, letInMap)
        if (bodyMap.isEmpty) {
          bodyMap
        } else {
          bodyMap + (ex.ID -> bodyMap.getOrElse(body.ID, Set(SortedSet.empty[UID])))
        }

      /**
       * Branches( /\ \phi_i ) = { Br_1 U ... U Br_s | \forall i . Br_i \in Branches(\phi_i) } { S \cap A | S \in
       * Branches( /\ phi_i ) } = { (Br_1 U ... U Br_s) \cap A | \forall i . Br_i \in Branches(\phi_i) } = { (Br_1 \cap
       * A) U ... U (Br_s \cap A) | \forall i . Br_i \in Branches(\phi_i) } = { B_1 U ... U B_n | \forall i . B_i \in {
       * T \cap A | T \in Branches(\phi_i)} }
       */
      case OperEx(TlaBoolOper.and, args @ _*) =>
        /** Unify all child maps, keysets are disjoint by construction */
        val unifiedMap = (args
          .map {
            allSelections(_, letInMap)
          })
          .fold(SortedMap.empty[UID, AssignmentSelections]) {
            _ ++ _
          }

        val childBranchSets = args.flatMap(x => unifiedMap.get(x.ID))

        /** The set as computed from the lemma */
        val mySet = allCombinations(childBranchSets)
        if (mySet.isEmpty || mySet.exists(_.isEmpty)) {
          unifiedMap
        } else {
          unifiedMap + (ex.ID -> mySet)
        }

      /**
       * Branches( \/ \phi_i ) = U Branches(\phi_i) { S \cap A | S \in Branches( \/ \phi_i )} = { S \cap A | S \in U
       * Branches(\phi_i)} = U { S \cap A | S \in Branches(\phi_i)}
       */
      case OperEx(TlaBoolOper.or, args @ _*) =>
        val unifiedMap = (args
          .map {
            allSelections(_, letInMap)
          })
          .fold(SortedMap.empty[UID, AssignmentSelections]) {
            _ ++ _
          }

        val childBranchSets = args.flatMap(x => unifiedMap.get(x.ID))

        val mySet = childBranchSets.fold(Set.empty[SortedSet[UID]])(_ ++ _)
        if (mySet.isEmpty || mySet.exists(_.isEmpty)) {
          unifiedMap
        } else {
          unifiedMap + (ex.ID -> mySet)
        }

      /**
       * Branches( \E x \in S . \phi ) = Branches( \phi ) { S \cap A | S \in Branches( \E x \in S . \phi )} = { S \cap A
       * \| S \in Branches( \phi )} =
       */
      case OperEx(TlaBoolOper.exists, _, _, phi) =>
        val childMap = allSelections(phi, letInMap)
        val mySet = childMap.getOrElse(phi.ID, Set(SortedSet.empty[UID]))
        if (mySet.exists(_.isEmpty)) childMap else childMap + (ex.ID -> mySet)

      /**
       * Branches( ITE(\phi_c, \phi_t, \phi_e) ) = Branches( \phi_t ) U Branches( \phi_e ) { S \cap A | S \in Branches(
       * ITE(\phi_c, \phi_t, \phi_e) )} = { S \cap A | S \in Branches( \phi_t ) U Branches( \phi_e ) } = { S \cap A | S
       * \in Branches( \phi_t ) } U { S \cap A | S \in Branches( \phi_e ) }
       */
      case OperEx(TlaControlOper.ifThenElse, _, thenAndElse @ _*) =>
        val unifiedMap = (thenAndElse
          .map {
            allSelections(_, letInMap)
          })
          .fold(SortedMap.empty[UID, AssignmentSelections]) { _ ++ _ }

        val childBranchSets = thenAndElse.flatMap(x => unifiedMap.get(x.ID))

        val mySet = childBranchSets.fold(Set[SortedSet[UID]]())(_ ++ _)
        if (mySet.isEmpty || mySet.exists(_.isEmpty)) {
          unifiedMap
        } else {
          unifiedMap + (ex.ID -> mySet)
        }

      case LetInEx(body, defs @ _*) =>
        val defMap = (defs.map { d =>
          d.name -> (d.body.ID, allSelections(d.body, letInMap))
        }).toMap
        val childMap = allSelections(body, letInMap ++ defMap)
        val mySet = childMap.getOrElse(body.ID, Set(SortedSet.empty[UID]))
        if (mySet.exists(_.isEmpty)) childMap else childMap + (ex.ID -> mySet)

      // Nullary apply
      case OperEx(TlaOper.apply, NameEx(operName)) =>
        // Apply may appear in higher order operators, so it might not be possible to pre-analyze
        letInMap.get(operName) match {
          case Some((uid, lim)) =>
            val mySet = lim.getOrElse(uid, Set(SortedSet.empty[UID]))
            if (mySet.exists(_.isEmpty)) lim else lim + (ex.ID -> mySet)
          case None => SortedMap.empty[UID, AssignmentSelections]
        }

      case _ => SortedMap.empty[UID, AssignmentSelections]
    }

    def sliceWith(selection: Set[UID], allSelections: SelMapType): TlaExTransformation = tracker.trackEx {
      // Assignments are a base case, don't recurse on args
      case ex @ OperEx(ApalacheOper.assign, _*)   => ex
      case ex @ OperEx(TlaBoolOper.or, args @ _*) =>
        /**
         * Or-branches have the property that they either contain all assignments or none of them. Therefore it suffices
         * to check for non-emptiness of the intersection.
         */
        /**
         * Jure, 16.9.19: This is no longer true, with the inclusion of LET-IN, as assignments that happen within a
         * LET-IN operator body can appear to belong to multiple branches.
         */

        val newArgs = args.filter { x =>
          /**
           * \E S \in allSelections( x ) . S \cap selection \ne \emptyset <=> \E S \in allSelections( x ) . \E y \in S .
           * y \in selection <=> \E S \in allSelections( x ) . \E y \in selection . y \in S <=> \E y \in selection . y
           * \in \bigcup allSelections( x )
           */
          labelsAt(x, allSelections).exists {
            selection.contains
          }
        }

//        /**
//          * If no assignments lie below, take the largest subformula.
//          * It is guaranteed to belong to the union of branches.
//          * Otherwise, take the one intersecting branch (recurse, since disjunctions aren't always expanded)
        //          */
        //        assert( newArgs.size < 2 )

        //        newArgs.headOption.map( sliceWith( selection, allSelections) ).getOrElse( ex )
        newArgs match {
          case Nil         => ex
          case head +: Nil => sliceWith(selection, allSelections)(head)
          case _           => OperEx(TlaBoolOper.or, newArgs.map(sliceWith(selection, allSelections)): _*)(ex.typeTag)
        }

      /**
       * We replace ITE(a,b,c) with either a /\ b or ~a /\ c, depending on which branch has the assignment. This only
       * applies if exactly branch has an assignment, otherwise keep all
       */
      case ex @ OperEx(TlaControlOper.ifThenElse, ifEx, args @ _*) =>
        val newTail = args.map(x =>
          if (
              labelsAt(x, allSelections).exists {
                selection.contains
              }
          )
            sliceWith(selection, allSelections)(x)
          else ValEx(TlaBool(false))(ex.typeTag))

        newTail match {
          case ValEx(TlaBool(false)) +: ValEx(TlaBool(false)) +: Nil =>
            ex
          case newThen +: (b @ ValEx(TlaBool(false))) +: Nil =>
            OperEx(TlaBoolOper.and, ifEx, newThen)(b.typeTag)
          case (b @ ValEx(TlaBool(false))) +: newElse +: Nil =>
            OperEx(TlaBoolOper.and, OperEx(TlaBoolOper.not, ifEx)(b.typeTag), newElse)(b.typeTag)
          case _ =>
            // Possible, because of LET-IN
            OperEx(TlaControlOper.ifThenElse, ifEx +: newTail: _*)(ex.typeTag)
        }

      case ex @ OperEx(op, args @ _*) =>
        val childVals = args.map {
          sliceWith(selection, allSelections)
        }
        // Make sure to avoid creating new UIDs if not absolutely needed, as filtering
        // is done on the basis of UIDs not syntax
        if (childVals == args) ex else OperEx(op, childVals: _*)(ex.typeTag)

      case ex @ LetInEx(body, defs @ _*) =>
        val slice = sliceWith(selection, allSelections)
        val newDefs = defs.map { d =>
          d.copy(body = slice(d.body))
        } // filterNot { _.body == ValEx( TlaFalse ) } ?

        val newBody = slice(body)

        val same = newDefs == defs && newBody == body

        if (same) ex
        else if (newBody == ValEx(TlaBool(false))(Typed(BoolT1))) newBody
        else LetInEx(newBody, newDefs: _*)(ex.typeTag)

      case ex => ex
    }

    /**
     * Orders a selection by \prec_A
     *
     * @param selection
     *   A selection S \subseteq A
     * @param strategy
     *   An assignment strategy A.
     * @return
     *   A sequence of elements s_1, ..., s_|S| from S, such that s_1 \prec_A ... \prec_A s_|S|
     */
    def mkOrdered(
        selection: Set[UID],
        strategy: StrategyType): AssignmentType = {
      strategy.filter(selection.contains) // strategy is already ordered
    }

    /**
     * Gathers the orderedAssignments selections and their corresponding restricted formulas.
     *
     * @param ex
     *   Input formula.
     * @param strategy
     *   Assignment strategy
     * @param selections
     *   Map of partial assignment selections.
     * @return
     *   A sequence of pairs of ordered assignment selections and their symbolic transitions.
     */
    private[SymbTransGenerator] def getTransitions(
        ex: TlaEx,
        strategy: StrategyType,
        selections: SortedSelMapType): Seq[SymbTrans] = {
      // It is crucial to have selections sorted here, to have a deterministic output.
      // Otherwise, `sliceWith` produces UIDs in different orders on different runs.
      // As a result, multiple runs of the same spec would produce different orderings of transitions,
      // which is highly undesirable.
      selections(ex.ID).toSeq.map { s =>
        (mkOrdered(s, strategy), sliceWith(s, selections)(ex))
      }
    }
  }

  /**
   * Given an expression `phi` and an assignment strategy `asgnStrategy`, computes a collection of symbolic transitions.
   *
   * @param phi
   *   TLA+ formula
   * @param asgnStrategy
   *   Assignment strategy A for `p_phi`.
   * @return
   *   A collection of symbolic transitions, as defined by the equivalence classes of ~,,A,,
   */
  def apply(phi: TlaEx, asgnStrategy: StrategyType): Seq[SymbTrans] = {

    import helperFunctions._

    /**
     * For certain purposes, we do not care about the order of assignments. It is therefore helpful to have a set
     * structure, with faster lookups.
     */
    val stratSet = asgnStrategy.toSet

    /** Replace all assignments */
    val asgnTransform = AssignmentOperatorIntroduction(stratSet, tracker)
    val transformed = asgnTransform(phi)

    /**
     * Since the new assignments have different UIDs, the new strategy is obtained by replacing the UIDs in the old
     * strategy (preserving order)
     */

    // In the case of manual assignments, return own UID (no need to populate the map)
    val newStrat = asgnStrategy.map { x => asgnTransform.getReplacements.getOrElse(x, x) }

    /** We compute the set of all branch intersections with `asgnStrategy` */
    val selections = allSelections(transformed, SortedMap.empty)

    /** Sanity check, all selections are the same size */
    val allSizes = selections(transformed.ID).map(s => s.size)
    assert(allSizes.size == 1)

    // now, it is quite important to sort the selections, to have a deterministic output
    val sortedSelections = selections.map { case (uid, selSet) =>
      (uid, SortedSet.empty[SortedSet[UID]](Ordering.fromLessThan(selectionLt)) ++ selSet)
    }

    /** We restrict the formula to each equivalence class (defined by an assignment selection) */
    getTransitions(transformed, newStrat, sortedSelections)
  }

  // A comparator for two selections. We do not use it by default, as it would probably be too slow.
  // We only use it in the end to sort the final selections.
  private def selectionLt(s1: SortedSet[UID], s2: SortedSet[UID]): Boolean = {
    if (s1.size < s2.size) {
      true
    } else if (s1.size > s2.size) {
      false
    } else {
      // compare the ids lexicographically
      for ((uid1, uid2) <- s1.zip(s2)) {
        if (uid1 < uid2) {
          return true
        } else if (uid1 > uid2) {
          return false
        }
      }

      false
    }
  }
}

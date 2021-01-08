package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory, SourceLocator}
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker


/**
  * Performs the complete procedure of finding symbolic transitions from the TLA+ implementation.
  *
  * Assignment candidates follow the assignment-before-use paradigm.
  *
  * @see [[SymbTransGenerator]]
  *
  */
class SmtFreeSymbolicTransitionExtractor(
                                          tracker: TransformationTracker,
                                          sourceLoc: SourceLocator
                                        ) {

  private def getLocString( ex: TlaEx ) = sourceLoc.sourceOf( ex ).getOrElse( "<[UNKNOWN]>" )

  /** Checks whether expressions, which cannot contain assignments, use unassigned variables */
  private def throwOnUseBeforeAssignment( unassignedVars: Set[String] ) : TlaEx => Unit = {
    /** Manual assignments at such locations throw exceptions */
    case ex@OperEx( BmcOper.assign, OperEx( TlaActionOper.prime, NameEx( _ ) ), _ ) =>
      val locString = getLocString( ex )
      // TODO: Update manual on assignments, see #368
      throw new AssignmentException(
        s"$locString: Illegal assignment inside an assignment-free expression. See ${SmtFreeSymbolicTransitionExtractor.MANUAL_LINK}"
      )
    case ex@OperEx( TlaActionOper.prime, NameEx( name ) ) if unassignedVars.contains( name ) =>
      val locString = getLocString( ex )
      // TODO: Update manual on assignments, see #368
      throw new AssignmentException( s"$locString: $name' is used before it is assigned. See ${SmtFreeSymbolicTransitionExtractor.MANUAL_LINK}" )
    case OperEx( _, args@_* ) =>
      args foreach throwOnUseBeforeAssignment( unassignedVars )
    case LetInEx( body, defs@_* ) =>
      defs foreach { d => throwOnUseBeforeAssignment( unassignedVars )( d.body ) }
      throwOnUseBeforeAssignment( unassignedVars )( body )
    case _ =>
  }

  // Partial state in the computation, with some subset of all variables already assigned and a partial strategy found
  private case class PartialState( unassignedVars: Set[String], partialStrat: StrategyType )

  // Since disjunction and ITE behave exactly the same w.r.t. assignments, we write a unified routine
  private def handleDisjunctionOrITE( s: PartialState, letInOperMap: BodyMap , args: Seq[TlaEx] ): PartialState = {
    // We independently process each disjunct
    val childStates = args map { getStrategyOptInternal(s, letInOperMap)(_) }
    val unassignedVarsSeq = childStates map { _.unassignedVars }
    // We need to see whether all branches assign exactly the same variables
    val unassignedEverywhere = unassignedVarsSeq.foldLeft( s.unassignedVars ){ _.intersect( _ ) }
    val unassignedSomewhere = unassignedVarsSeq.foldLeft( Set.empty[String] ) { _.union( _ ) }
    // Variables that are unassigned on at least one branch and assigned on all others
    val imbalancedAssignments = unassignedSomewhere -- unassignedEverywhere
    if (imbalancedAssignments.nonEmpty) {
      // Report problms for each disjunct, if any
      val problems : Seq[String] = args.zip( childStates ) flatMap {
        case (childEx, PartialState( childUnassignedVars, _ )) =>
          val s = childUnassignedVars.intersect( imbalancedAssignments )
          if ( s.isEmpty ) None
          else {
            val locString = getLocString( childEx )
            Some( s"$locString: Missing assignments to: ${s.mkString( "," )}" )
          }
      }

      throw new AssignmentException( problems.mkString("\n") )
    }
    // Assuming all branches assign the same variables, works correctly if args.isEmpty (for whatever reason)
    val unifiedStrat = (childStates map { _.partialStrat }).foldLeft( s.partialStrat ) { _ ++ _ }
    PartialState( unassignedEverywhere, unifiedStrat )
  }

  // Transition method between partial states
  private def getStrategyOptInternal( currentState: PartialState, letInOperMap: BodyMap ): TlaEx => PartialState = {
    /** Base case, assignment candidates  */
    case ex@OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( name ) ), assignmentFreeRhs ) =>
      // First, check if assignmentFreeRhs contains unassigned varaible access
      throwOnUseBeforeAssignment( currentState.unassignedVars )( assignmentFreeRhs )
      // if `name` is not yet assigned, this spot becomes an assignment
      if ( currentState.unassignedVars.contains( name ))
        PartialState( currentState.unassignedVars - name, currentState.partialStrat :+ ex.ID )
      else currentState

    /** Base case, manual assignments */
    case ex@OperEx( BmcOper.assign, OperEx( TlaActionOper.prime, NameEx( name ) ), assignmentFreeRhs ) =>
      // Similar to above, except manual assignments throw if spurious
      throwOnUseBeforeAssignment( currentState.unassignedVars )( assignmentFreeRhs )
      if ( currentState.unassignedVars.contains( name ))
        PartialState( currentState.unassignedVars - name, currentState.partialStrat :+ ex.ID )
      else {
        val locString = getLocString( ex )
        // TODO: Update manual on assignments, see #368
        throw new AssignmentException(
          s"$locString: Manual assignment is spurious, $name is already assigned! See ${SmtFreeSymbolicTransitionExtractor.MANUAL_LINK}"
        )
      }

    /** Conjunction */
    case OperEx( TlaBoolOper.and, args@_* ) =>
      // We sequentially update the partial state
      args.foldLeft( currentState ) { getStrategyOptInternal(_, letInOperMap)(_) }
    /** Disjunction */
    case ex@OperEx( TlaBoolOper.or, args@_* ) =>
      handleDisjunctionOrITE( currentState, letInOperMap,  args)

    /** \E quantifier */
    case OperEx( TlaBoolOper.exists, NameEx( _ ), assignmentFreeSetEx, subEx ) =>
      // We need to check that assignmentFreeSetEx does not contain unassigned primes.
      throwOnUseBeforeAssignment( currentState.unassignedVars )( assignmentFreeSetEx )
      // if no exception is thrown, continue in subEx
      getStrategyOptInternal( currentState, letInOperMap )( subEx )


    /** ITE */
    case OperEx( TlaControlOper.ifThenElse, assignmentFreeCond, thenAndElse@_* ) =>
      // We need to check that assignmentFreeCond does not contain unassigned primes.
      throwOnUseBeforeAssignment( currentState.unassignedVars )( assignmentFreeCond )
      // The rest is equivalent to the disjunction case
      handleDisjunctionOrITE( currentState, letInOperMap, thenAndElse)

    /** Nullary LetIn */
    case LetInEx( body, defs@_* ) =>
      // Sanity check, all operators must be nullary and non-recursive
      assert( defs.forall { d => d.formalParams.isEmpty && !d.isRecursive } )
      // We memorize the let-in operators, to recall when we see an apply
      val newMap = BodyMapFactory.makeFromDecls( defs, letInOperMap)
      // finally, we check the let-in body as well
      getStrategyOptInternal( currentState, newMap )( body )

    /** Nullary apply */
    case OperEx( TlaOper.apply, NameEx(operName) ) =>
      // If the body is known ( i.e. introduced by LET-IN ), we read it from the map
      val knownBodyOpt = letInOperMap.get( operName ) map { _.body }
      val newStateOpt = knownBodyOpt map { getStrategyOptInternal(currentState, letInOperMap)(_) }
      // In all other cases, the operator application cannot introduce assignments
      newStateOpt.getOrElse( currentState )

    /** Misc. operator */
    case OperEx( _, args@_* ) =>
      // For other operators, make sure they don't use unassigned variables ...
      args foreach throwOnUseBeforeAssignment( currentState.unassignedVars )
      // ... but don't update assignments
      currentState
    /** In the other cases, return the default args */
    case _ => currentState
  }

  def getStrategy(vars: Set[String], actionEx: TlaEx): StrategyType = {
    // The strategy can be extracted from the state obtained by starting from the initial state, where
    //   - all variables in `vars` are unassigned
    //   - no partial strategy has been found
    //   - no let-in defined operators are known
    val finalState = getStrategyOptInternal( PartialState( vars, Seq.empty ), Map.empty )( actionEx )
    // There is a possibility that some variables never get assigned at all
    val missingVars = finalState.unassignedVars
    // If any are missing, throw, otherwise the final partial strategy is the solution
    if (missingVars.nonEmpty) throw new AssignmentException(s"No assignments found for: ${missingVars.mkString(", ")}")
    else finalState.partialStrat
  }

  /**
    * Find assignments in an action expression and produce symbolic transitions, if possible.
    *
    * @param vars names of the variables on which actionExpr is operating, e.g, the variables defined with VARIABLES
    * @param actionExpr an expression over primed and unprimed variables, e.g., Next or Init
    * @return A collection of symbolic transitions, if they can be extracted
    *
    */
  def apply(vars: Set[String], actionExpr: TlaEx) : Seq[SymbTrans] = {
    /** Get strategy from the actionExpr */
    val assignmentStrategy = getStrategy( vars, actionExpr )
    val stg = new SymbTransGenerator( tracker )
    stg( actionExpr, assignmentStrategy )
  }

}

object SmtFreeSymbolicTransitionExtractor {
  val MANUAL_LINK = "https://apalache.informal.systems/docs/apalache/principles.html#assignments"

  def apply(tracker: TransformationTracker, sourceLoc: SourceLocator): SmtFreeSymbolicTransitionExtractor = {
    new SmtFreeSymbolicTransitionExtractor(tracker, sourceLoc)
  }
}


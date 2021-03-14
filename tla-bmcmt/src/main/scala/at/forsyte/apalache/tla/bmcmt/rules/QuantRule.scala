package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, OracleHelper}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Rewrites \A x \in S: P and \E x \in S: P. The existential quantifier is often replaced with a constant (skolemized).
 *
 * @author Igor Konnov
 */
class QuantRule(rewriter: SymbStateRewriter) extends RewritingRule with LazyLogging {
  private val pickRule = new CherryPick(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.exists, _, _, _)                           => true
      case OperEx(BmcOper.`skolem`, OperEx(TlaBoolOper.exists, _, _, _)) => true
      case OperEx(TlaBoolOper.forall, _, _, _)                           => true
      case _                                                             => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(BmcOper.`skolem`, OperEx(TlaBoolOper.exists, NameEx(boundVar), boundingSetEx, predEx)) =>
        // This is where our encoding shines. An existential is simply replaced by a constant.
        boundingSetEx match {
          case ValEx(TlaNatSet) | ValEx(TlaIntSet) =>
            // skolemizable existential over integers or naturals
            skolemExistsInNatOrInt(state, boundVar, predEx, boundingSetEx)

          case OperEx(TlaArithOper.dotdot, left, right) =>
            // rewrite \E x \in a..b: p as c >= a /\ c <= b /\ p[c/x] for an integer constant c
            skolemExistsInRange(state, boundVar, predEx, left, right)

          // the general case
          case _ =>
            val setState = rewriter.rewriteUntilDone(state.setRex(boundingSetEx))
            val set = setState.asCell
            set.cellType match {
              case FinSetT(_) =>
                skolemExistsInSet(setState, boundVar, predEx, set)

              case PowSetT(FinSetT(_)) =>
                ()
                skolemExistsByPick(setState, boundVar, predEx, set)

              case FinFunSetT(_, _) =>
                ()
                skolemExistsByPick(setState, boundVar, predEx, set)

              case tp =>
                throw new UnsupportedOperationException("Quantification over %s is not supported yet".format(tp))
            }
        }

      case OperEx(TlaBoolOper.exists, NameEx(boundVar), boundingSetEx, predEx) =>
        // expand the existential to a disjunction
        expandExistsOrForall(isExists = true, state, boundVar, boundingSetEx, predEx)

      case OperEx(TlaBoolOper.forall, NameEx(boundVar), boundingSetEx, predEx) =>
        // expand the existential to a conjunction
        expandExistsOrForall(isExists = false, state, boundVar, boundingSetEx, predEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def isAssignmentInside(ex: TlaEx): Boolean = ex match {
    case OperEx(BmcOper.assign, OperEx(TlaActionOper.prime, NameEx(_)), _) => true
    case OperEx(_, args @ _*)                                              => args.exists(isAssignmentInside)
    case _                                                                 => false
  }

  private def expandExistsOrForall(isExists: Boolean, state: SymbState, boundVar: String, boundingSetEx: TlaEx,
      predEx: TlaEx) = {
    rewriter.solverContext.log("; quantification over a finite set => expanding")

    if (isAssignmentInside(predEx)) {
      val msg =
        if (isExists) {
          "Assignments inside \\E are currently supported only for skolemizable existentials"
        } else {
          "Assignments inside \\A do not make any sense!"
        }

      throw new NotImplementedError(msg)
    }

    // first, evaluate boundingSet
    val setState = rewriter.rewriteUntilDone(state.setRex(boundingSetEx))
    val set = setState.arena.findCellByNameEx(setState.ex)
    set.cellType match {
      case FinSetT(_) => () // supported

      case tp =>
        val msg = "Trying to expand a complex set in \\E %s \\in ... ".format(boundVar) +
          "Try to move \\E out of a negated expression. Expression: "
        logger.warn(msg)
        throw new UnsupportedOperationException("Expansion of %s is not supported yet".format(tp))
    }
    val setCells = setState.arena.getHas(set)
    if (setCells.isEmpty) {
      // 'exists' over an empty set always returns false, while 'forall' returns true
      val constResult =
        if (isExists)
          setState.arena.cellFalse()
        else
          setState.arena.cellTrue()

      setState.setRex(constResult.toNameEx)
    } else {
      def mkPair(elemCell: ArenaCell): (Binding, TlaEx) = {
        val newBinding = Binding(setState.binding.toMap + (boundVar -> elemCell))
        (newBinding, predEx)
      }

      // rewrite p[c_i/x] for every c_i \in boundingSet
      val (predState: SymbState, predEs: Seq[TlaEx]) =
        rewriter.rewriteBoundSeqUntilDone(setState, setCells.map(mkPair))

      val nonEmpty = tla.or(setCells.map(c => tla.in(c.toNameEx, set.toNameEx)): _*)
      val empty = tla.and(setCells.map(c => tla.not(tla.in(c.toNameEx, set.toNameEx))): _*)

      def elemWitnesses(elemAndPred: (ArenaCell, TlaEx)): TlaEx = {
        tla.and(tla.in(elemAndPred._1.toNameEx, set.toNameEx), elemAndPred._2)
      }

      def elemSatisfies(elemAndPred: (ArenaCell, TlaEx)): TlaEx = {
        tla.or(tla.not(tla.in(elemAndPred._1.toNameEx, set.toNameEx)), elemAndPred._2)
      }

      var finalState = predState.updateArena(_.appendCell(BoolT()))
      val pred = finalState.arena.topCell
      val iff =
        if (isExists) {
          // \E x \in S: p holds iff nonEmpty /\ \/_i (p[c_i/x] /\ c_i \in set)
          val existsElem = tla.or(setCells.zip(predEs).map(elemWitnesses): _*)
          tla.equiv(pred.toNameEx, tla.and(nonEmpty, existsElem))
        } else {
          // \A x \in S: p holds iff empty \/ /\_i (p[c_i/x] \/ ~c_i \in set)
          val allElem = tla.and(setCells.zip(predEs).map(elemSatisfies): _*)
          tla.equiv(pred.toNameEx, tla.or(empty, allElem))
        }

      rewriter.solverContext.assertGroundExpr(iff)

      finalState
        .setRex(pred.toNameEx)
        .setBinding(Binding(predState.binding.toMap - boundVar)) // forget the binding to x, but not the other bindings!
    }
  }

  private def skolemExistsInNatOrInt(state: SymbState, boundVar: String, predEx: TlaEx,
      boundingSetEx: TlaEx): SymbState = {
    rewriter.solverContext.log("; free existential rule over an infinite set " + boundingSetEx)
    var nextState = state.setArena(state.arena.appendCell(IntT()))
    val witness = nextState.arena.topCell
    if (boundingSetEx == ValEx(TlaNatSet)) {
      rewriter.solverContext.assertGroundExpr(tla.ge(witness.toNameEx, tla.int(0)))
    }
    // enforce that the witness satisfies the predicate
    val extendedBinding = Binding(nextState.binding.toMap + (boundVar -> witness))
    // predState.ex contains the predicate applied to the witness
    nextState = rewriter.rewriteUntilDone(
        nextState
          .setRex(predEx)
          .setBinding(extendedBinding))
    nextState
      .setBinding(Binding(nextState.binding.toMap - boundVar)) // forget the binding to x, but not the other bindings!
  }

  private def skolemExistsInRange(state: SymbState, boundVar: String, predEx: TlaEx, leftBound: TlaEx,
      rightBound: TlaEx): SymbState = {
    rewriter.solverContext.log(s"; skolemizable existential $boundVar over $leftBound..$rightBound ")
    var nextState = state.setArena(state.arena.appendCell(IntT()))
    val witness = nextState.arena.topCell
    // assert that the witness is in the range leftBound..rightBound
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.ge(witness.toNameEx, leftBound)))
    rewriter.solverContext.assertGroundExpr(nextState.ex)
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.le(witness.toNameEx, rightBound)))
    rewriter.solverContext.assertGroundExpr(nextState.ex)
    // enforce that the witness satisfies the predicate
    val extendedBinding = Binding(nextState.binding.toMap + (boundVar -> witness))
    // predState.ex contains the predicate applied to the witness
    nextState = rewriter.rewriteUntilDone(
        nextState
          .setRex(predEx)
          .setBinding(extendedBinding))
    nextState
      .setBinding(Binding(nextState.binding.toMap - boundVar)) // forget the binding to x, but not the other bindings!
  }

  private def skolemExistsInSet(setState: SymbState, boundVar: String, predEx: TlaEx, set: ArenaCell) = {
    val setCells = setState.arena.getHas(set)
    if (setCells.isEmpty) {
      // \E x \in {}... is FALSE
      setState.setRex(setState.arena.cellFalse().toNameEx)
    } else {
      skolemExistsInStaticallyNonEmptySet(setState, boundVar, predEx, set, setCells)
    }
  }

  // Introduce a Skolem constant for a free-standing existential quantifier:
  // that is, rewrite, \E x \in S: P(x) as S /= {} /\ P(c) for a constant c picked from S.
  //
  // We have to take care of the case, when the set S is actually empty, e.g., S = {1} \ {1}.
  // In this case, exists should return FALSE.
  private def skolemExistsInStaticallyNonEmptySet(setState: SymbState, boundVar: String, predEx: TlaEx, set: ArenaCell,
      setCells: List[ArenaCell]) = {
    // note that \E x \in SUBSET(S): ... is handled separately, so we can use pickByOracle
    rewriter.solverContext.log("; free existential rule over a finite set")
    // choose an oracle with the default case oracle = N, when the set is empty
    val (oracleState, oracle) = pickRule.oracleFactory.newDefaultOracle(setState, setCells.size + 1)
    var nextState = oracleState
    OracleHelper.assertOraclePicksSetMembers(rewriter, nextState, oracle, set, setCells)
    // pick an arbitrary witness according to the oracle
    nextState = pickRule.pickByOracle(nextState, oracle, setCells, nextState.arena.cellTrue().toNameEx)
    val pickedCell = nextState.asCell
    // enforce that the witness satisfies the predicate
    val extendedBinding = Binding(nextState.binding.toMap + (boundVar -> pickedCell))
    // predState.ex contains the predicate applied to the witness
    nextState = rewriter.rewriteUntilDone(
        nextState
          .setRex(predEx)
          .setBinding(extendedBinding))
    val predWitness = nextState.ex

    // \E x \in S: p holds iff predWitness /\ S /= {}
    nextState = nextState.updateArena(_.appendCell(BoolT()))
    val exPred = nextState.arena.topCell
    val setNonEmpty = tla.not(oracle.whenEqualTo(nextState, setCells.size))
    val iff = tla.equiv(exPred.toNameEx, tla.and(setNonEmpty, predWitness))
    rewriter.solverContext.assertGroundExpr(iff)

    nextState
      .setRex(exPred.toNameEx)
      .setBinding(Binding(nextState.binding.toMap - boundVar)) // forget the binding to x, but not the other bindings!
  }

  // Introduce a Skolem constant for a free-standing existential quantifier:
  // In case of SUBSET(S), it is really easy: we have to enforce that a witness is a subset of S.
  // A powerset is never empty, so we do not have to worry about this case.
  private def skolemExistsByPick(setState: SymbState, boundVar: String, predEx: TlaEx, set: ArenaCell) = {
    rewriter.solverContext.log("; free existential rule over " + set.cellType)
    // pick an arbitrary witness
    val pickState = pickRule.pick(set, setState, setState.arena.cellFalse().toNameEx)
    val pickedCell = pickState.arena.findCellByNameEx(pickState.ex)
    // enforce that the witness satisfies the predicate
    val extendedBinding = Binding(pickState.binding.toMap + (boundVar -> pickedCell))
    // predState.ex contains the predicate applied to the witness
    val predState = rewriter.rewriteUntilDone(
        pickState
          .setRex(predEx)
          .setBinding(extendedBinding))
    val predWitness = predState.ex

    predState
      .setRex(predWitness)
      .setBinding(Binding(predState.binding.toMap - boundVar)) // forget the binding to x, but not the other bindings!
  }
}

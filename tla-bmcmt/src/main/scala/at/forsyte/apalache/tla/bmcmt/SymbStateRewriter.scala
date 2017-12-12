package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.bmcmt.rules._
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

object SymbStateRewriter {
  sealed abstract class RewritingResult

  case class Done(symbState: SymbState) extends RewritingResult

  case class Continue(symbState: SymbState) extends RewritingResult

  case class NoRule() extends RewritingResult
}

/**
  * This class rewrites a symbolic state.
  * This is the place where all the action regarding the operational semantics is happening.
  *
  * @author Igor Konnov
  */
class SymbStateRewriter {
  val lazyEquality = new LazyEquality(this)
  // don't try to rewrite the same rule more than RECURSION_LIMIT times
  private val RECURSION_LIMIT: Int = 1000000
  private val coercion = new Coercion(this)
  private val substRule = new SubstRule(this)
  private val rules =
    List(substRule, new BoolConstRule(this), new IntConstRule(this),
      new EqRule(this), new NeqRule(this),
      new OrRule(this), new AndRule(this), new NegRule(this),
      new IntCmpRule(this), new IntArithRule(this),
      new SetCtorRule(this), new TupleCtorRule(this),
      new SetInRule(this), new SetNotInRule(this),
      new SetCupRule(this), new SetCapAndMinusRule(this),
      new SetFilterRule(this), new SetMapAndFunCtorRule(this), new FunAppRule(this),
      new IntDotDotRule(this)
    ) /////////////

  def rewriteOnce(state: SymbState): RewritingResult = {
    state.ex match {
      case NameEx(name) if CellTheory().hasConst(name) =>
        Done(coerce(state.setTheory(CellTheory()), state.theory))

      case NameEx(name) if BoolTheory().hasConst(name) =>
        Done(coerce(state.setTheory(BoolTheory()), state.theory))

      case NameEx(name) if IntTheory().hasConst(name) =>
        Done(coerce(state.setTheory(IntTheory()), state.theory))

      case NameEx(name) =>
        if (substRule.isApplicable(state)) {
          // a variable that can be substituted with a cell
          substRule.logOnEntry(state)
          Done(substRule.logOnReturn(coerce(substRule.apply(state), state.theory)))
        } else {
          // oh-oh
          NoRule()
        }

      case _ =>
        // TODO: can we do any better than just a linear search?
        rules.find(r => r.isApplicable(state)) match {
          case Some(r) =>
            r.logOnEntry(state)
            Continue(r.logOnReturn(r.apply(state)))

          case None =>
            NoRule()
        }
    }
  }

  /**
    * Rewrite one expression until converged, or no rule applies.
    *
    * @param state a state to rewrite
    * @return the final state
    * @throws RewriterException if no rule applies
    */
  def rewriteUntilDone(state: SymbState): SymbState = {
    def doRecursive(ncalls: Int, st: SymbState): SymbState = {
      if (ncalls >= RECURSION_LIMIT) {
        throw new RewriterException("Recursion limit reached. A bug in the rewriting system?")
      } else {
        rewriteOnce(st) match {
          case Done(nextState) =>
            // converged to the normal form
            nextState

          case Continue(nextState) =>
            // more translation steps are needed
            // TODO: place a guard on the number of recursive calls
            doRecursive(ncalls + 1, nextState)

          case NoRule() =>
            // no rule applies, a problem in the tool?
            throw new RewriterException("No rule applies to expression: " + st.ex)
        }
      }
    }
    doRecursive(0, state)
  }

  /**
    * Rewrite all expressions in a sequence.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite
    * @return a pair (the old state in a new context, the rewritten expressions)
    */
  def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
    def process(st: SymbState, seq: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case r :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val ns = rewriteUntilDone(new SymbState(r, ts.theory, ts.arena, ts.binding, ts.solverCtx))
          (ns, ns.ex :: nt)
      }
    }

    val pair = process(state, es.toList)
    (pair._1.setRex(state.ex), pair._2)
  }

  /**
    * Coerce the state expression from the current theory to another theory.
    *
    * @param state a symbolic state
    * @param targetTheory a target theory
    * @return a new symbolic state, if possible
    */
  def coerce(state: SymbState, targetTheory: Theory): SymbState = {
    coercion.coerce(state, targetTheory)
  }
}

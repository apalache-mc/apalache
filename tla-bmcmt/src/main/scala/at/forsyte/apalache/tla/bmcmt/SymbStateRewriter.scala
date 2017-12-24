package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.bmcmt.rules._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

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
  * This class implements StackableContext by delegating the respective operations to all the internal caches
  * and the SMT context. Thus, it is a central access point for context operations.
  *
  * @author Igor Konnov
  */
class SymbStateRewriter(val solverContext: SolverContext) extends StackableContext {
  /**
    * The difference between the number of pushes and pops so far.
    */
  private var level: Int = 0

  /**
    * The cache for lazy equalities, to avoid generating the same equality constraints many times.
    */
  val lazyEq = new LazyEquality(this)

  /**
    * A cache for integer literals.
    */
  val intValueCache = new IntValueCache(solverContext)

  // bound the number of rewriting steps applied to the same rule
  private val RECURSION_LIMIT: Int = 10000
  private val coercion = new Coercion(this)
  private val substRule = new SubstRule(this)

  // A nice way to guess the candidate rules by looking at the expression key.
  // We use simple expressions to generate the keys.
  // The idea is similar to a hash table, but in contrast to a hash table,
  // we group similar expressions, since they have to be processed by the same rules.
  private val ruleLookupTable: Map[String, List[RewritingRule]] = Map(
    // the order is only important to improve readability

    // substitution
    key(NameEx("x"))
      -> List(substRule),
    key(tla.prime(NameEx("x")))
      -> List(new PrimeRule(this)),

    // constants
    key(ValEx(TlaBool(true)))
      -> List(new BoolConstRule(this)),
    key(ValEx(TlaInt(1)))
      -> List(new IntConstRule(this)),

    // logic
    key(tla.eql(tla.name("x"), tla.name("y")))
      -> List(new EqRule(this)),
    key(tla.neql(tla.name("x"), tla.name("y")))
      -> List(new NeqRule(this)),
    key(tla.or(tla.name("x"), tla.name("y")))
      -> List(new OrRule(this)),
    key(tla.and(tla.name("x"), tla.name("y")))
      -> List(new AndRule(this)),
    key(tla.not(tla.name("x")))
      -> List(new NegRule(this)),
    key(tla.exists(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new QuantRule(this)),
    key(tla.forall(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new QuantRule(this)),

    // control flow
    key(tla.ite(tla.name("cond"), tla.name("then"), tla.name("else")))
      -> List(new IfThenElseRule(this)),

    // sets
    key(tla.in(tla.name("x"), tla.name("S")))
      -> List(new AssignmentRule(this), new SetInRule(this)),
    key(tla.notin(tla.name("x"), tla.name("S")))
      -> List(new SetNotInRule(this)),
    key(tla.enumSet(tla.name("x"))) ->
      List(new SetCtorRule(this)),
    key(tla.subseteq(tla.name("x"), tla.name("S")))
      -> List(new SetInclusionRule(this)),
    key(tla.subset(tla.name("x"), tla.name("S")))
      -> List(new SetInclusionRule(this)),
    key(tla.supseteq(tla.name("x"), tla.name("S")))
      -> List(new SetInclusionRule(this)),
    key(tla.supset(tla.name("x"), tla.name("S")))
      -> List(new SetInclusionRule(this)),
    key(tla.cup(tla.name("X"), tla.name("Y")))
      -> List(new SetCupRule(this)),
    key(tla.cap(tla.name("X"), tla.name("Y")))
      -> List(new SetCapAndMinusRule(this)),
    key(tla.setminus(tla.name("X"), tla.name("Y")))
      -> List(new SetCapAndMinusRule(this)),
    key(tla.filter(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new SetFilterRule(this)),
    key(tla.map(tla.name("e"), tla.name("x"), tla.name("S")))
      -> List(new SetMapAndFunCtorRule(this)),
    key(tla.powSet(tla.name("X")))
      -> List(new PowSetCtorRule(this)),
    key(tla.dotdot(tla.int(1), tla.int(10)))
      -> List(new IntDotDotRule(this)),

    // integers
    key(tla.lt(tla.int(1), tla.int(2)))
      -> List(new IntCmpRule(this)),
    key(tla.le(tla.int(1), tla.int(2)))
      -> List(new IntCmpRule(this)),
    key(tla.gt(tla.int(1), tla.int(2)))
      -> List(new IntCmpRule(this)),
    key(tla.ge(tla.int(1), tla.int(2)))
      -> List(new IntCmpRule(this)),
    key(tla.plus(tla.int(1), tla.int(2)))
      -> List(new IntArithRule(this)),
    key(tla.minus(tla.int(1), tla.int(2)))
      -> List(new IntArithRule(this)),
    key(tla.mult(tla.int(1), tla.int(2)))
      -> List(new IntArithRule(this)),
    key(tla.div(tla.int(1), tla.int(2)))
      -> List(new IntArithRule(this)),
    key(tla.mod(tla.int(1), tla.int(2)))
      -> List(new IntArithRule(this)),

    // functions
    key(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S")))
      -> List(new SetMapAndFunCtorRule(this)),
    key(tla.appFun(tla.name("f"), tla.name("x")))
      -> List(new FunAppRule(this)),
    key(tla.except(tla.name("f"), tla.int(1), tla.int(42)))
      -> List(new FunExceptRule(this)),
    key(tla.funSet(tla.name("X"), tla.name("Y")))
      -> List(new FunSetCtorRule(this)),

    // tuples and records
    key(tla.tuple(tla.name("x"), tla.int(2)))
    -> List(new TupleCtorRule(this))
  )///// ADD YOUR RULES ABOVE

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    * @return the current level, always non-negative.
    */
  def contextLevel: Int = level


  /**
    * Rewrite a symbolic expression by applying at most one rewriting rule.
    * @param state a symbolic state
    * @return the new symbolic state obtained by rewriting state
    */
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
          substRule.logOnEntry(solverContext, state)
          Done(substRule.logOnReturn(solverContext, coerce(substRule.apply(state), state.theory)))
        } else {
          // oh-oh
          NoRule()
        }

      case _ =>
        // lookup for a short list of potentially applicable rules
        val potentialRules = ruleLookupTable.getOrElse(key(state.ex), List())

        potentialRules.find(r => r.isApplicable(state)) match {
          case Some(r) =>
            Continue(r.logOnReturn(solverContext, r.apply(r.logOnEntry(solverContext, state))))

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
        throw new RewriterException("Recursion limit of %d steps is reached. A cycle in the rewriting system?"
          .format(RECURSION_LIMIT))
      } else {
        rewriteOnce(st) match {
          case Done(nextState) =>
            // converged to the normal form
            nextState

          case Continue(nextState) =>
            // more translation steps are needed
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
          val ns = rewriteUntilDone(new SymbState(r, ts.theory, ts.arena, ts.binding))
          (ns, ns.ex :: nt)
      }
    }

    val pair = process(state, es.toList)
    (pair._1.setRex(state.ex), pair._2)
  }

  /**
    * An extended version of rewriteSeqUntilDone, where expressions are accompanied with bindings.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite accompanied with bindings
    * @return a pair (the old state in a new context, the rewritten expressions)
    */
  def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
    def process(st: SymbState, seq: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case p :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val ns = rewriteUntilDone(new SymbState(p._2, ts.theory, ts.arena, p._1))
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


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    level += 1
    intValueCache.push()
    lazyEq.push()
    solverContext.push()
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    assert(level > 0)
    intValueCache.pop()
    lazyEq.pop()
    solverContext.pop()
    level -= 1
  }

  /**
    * Call pop several times.
    *
    * @param n the number of times to call pop
    */
  override def pop(n: Int): Unit = {
    assert(level >= n)
    intValueCache.pop(n)
    lazyEq.pop(n)
    solverContext.pop(n)
    level -= n
  }

  /**
    * Clean the context
    */
  override def dispose(): Unit = {
    intValueCache.dispose()
    lazyEq.dispose()
    solverContext.dispose()
  }

  /**
    * Compute a key of a TLA+ expression to quickly decide on a short sequence of rules to try.
    * @param ex a TLA+ expression
    * @return a string that gives us an equivalence class for similar operations (see the code)
    */
  private def key(ex: TlaEx): String = {
    ex match {
      case OperEx(oper, _*) =>
        "O@" + oper.toString

      case ValEx(TlaInt(_)) | ValEx(TlaIntSet) =>
        "I@"

      case ValEx(TlaBool(_)) | ValEx(TlaBoolSet) =>
        "B@"

      case NameEx(_) =>
        "N@"

      case _ =>
        "O@"
    }
  }
}

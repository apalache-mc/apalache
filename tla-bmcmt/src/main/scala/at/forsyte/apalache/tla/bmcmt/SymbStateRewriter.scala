package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGrade, ExprGradeStoreImpl, FreeExistentialsStore, FreeExistentialsStoreImpl}
import at.forsyte.apalache.tla.bmcmt.caches.{ExprCache, IntValueCache, RecordDomainCache, StrValueCache}
import at.forsyte.apalache.tla.bmcmt.rules._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{AnyArity, TlaOper, TlcOper}
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

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

  /**
    * A cache for string literals.
    */
  val strValueCache = new StrValueCache(solverContext)

  /**
    * A cache of record domains.
    */
  val recordDomainCache = new RecordDomainCache(solverContext, strValueCache)

  /**
    * An expression cache that is initialized by grade storage, by default, empty.
    * Set it to a new object, if you want to use a grade storage.
    */
  var exprCache = new ExprCache(new ExprGradeStoreImpl())

  // bound the number of rewriting steps applied to the same rule
  private val RECURSION_LIMIT: Int = 10000
  private val coercion = new CoercionWithCache(this)
  private val substRule = new SubstRule(this)

  /**
    * The store that marks free existential quantifiers. By default, empty.
    */
  var freeExistentialsStore: FreeExistentialsStore = new FreeExistentialsStoreImpl()

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  def contextLevel: Int = level

  // A nice way to guess the candidate rules by looking at the expression key.
  // We use simple expressions to generate the keys.
  // For each key, there is a short list of rules that may be applicable.
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
    key(ValEx(TlaStr("red")))
      -> List(new StrConstRule(this)),

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
    key(tla.caseOther(tla.name("otherAction"), tla.name("pred1"), tla.name("action1")))
      -> List(new CaseRule(this)),
    key(tla.letIn(tla.int(1), TlaOperDecl("A", List(), tla.int(2))))
      -> List(new LetInRule(this)),
    key(OperEx(new TlaUserOper("userOp", AnyArity(), TlaOperDecl("userOp", List(), tla.int(3)))))
      -> List(new UserOperRule(this)),

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
    key(tla.union(tla.enumSet()))
      -> List(new SetUnionRule(this)),
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
    key(tla.exp(tla.int(2), tla.int(3)))
      -> List(new IntArithRule(this)),
    key(tla.uminus(tla.int(1)))
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
    key(tla.dom(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S"))))
      -> List(new DomainRule(this)), // also works for records

    // tuples and records
    key(tla.tuple(tla.name("x"), tla.int(2)))
      -> List(new TupleCtorRule(this)),
    key(tla.enumFun(tla.str("a"), tla.int(2)))
      -> List(new RecCtorRule(this)),

    // misc
    key(OperEx(TlaOper.label, tla.str("a"), tla.int(1)))
      -> List(new LabelRule(this)),

    // TLC
    key(OperEx(TlcOper.print, tla.bool(true), tla.str("msg")))
      -> List(new TlcRule(this)),
    key(OperEx(TlcOper.printT, tla.str("msg")))
      -> List(new TlcRule(this)),
    key(OperEx(TlcOper.assert, tla.bool(true), tla.str("msg")))
      -> List(new TlcRule(this))
  ) ///// ADD YOUR RULES ABOVE


  /**
    * Rewrite a symbolic expression by applying at most one rewriting rule.
    *
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
          val coercedState = coerce(substRule.apply(substRule.logOnEntry(solverContext, state)), state.theory)
          val nextState = substRule.logOnReturn(solverContext, coercedState)
          if (nextState.arena.cellCount < state.arena.cellCount) {
            throw new RewriterException("Implementation error: the number of cells decreased from %d to %d"
              .format(state.arena.cellCount, nextState.arena.cellCount))
          }
          Done(nextState)
        } else {
          // oh-oh
          NoRule()
        }

      case _ =>
        // lookup for a short list of potentially applicable rules
        val potentialRules = ruleLookupTable.getOrElse(key(state.ex), List())

        potentialRules.find(r => r.isApplicable(state)) match {
          case Some(r) =>
            //            try {
            val nextState = r.logOnReturn(solverContext, r.apply(r.logOnEntry(solverContext, state)))
            if (nextState.arena.cellCount < state.arena.cellCount) {
              throw new RewriterException("Implementation error in rule %s: the number of cells decreased from %d to %d"
                .format(r.getClass.getSimpleName, state.arena.cellCount, nextState.arena.cellCount))
            }
            Continue(nextState)
          //            } catch {
          //              case ub: UndefinedBehaviorError if state.theory == BoolTheory() =>
          //                // replace with an unrestricted Boolean
          //              solverContext.log("; Rolled back undefined behavior, #cells in arena: " + state.arena.cellCount)
          //                // bugfix: use fresh arena
          //              Done(mkNondetBool(state.setArena(ub.arena)))
          //            }

          case None =>
            NoRule()
        }
    }
  }

  private def mkNondetBool(state: SymbState): SymbState = {
    val bool = solverContext.introBoolConst()
    state.setTheory(BoolTheory()).setRex(NameEx(bool))
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
            throw new RewriterException("No rewriting rule applies to expression: " + st.ex)
        }
      }
    }

    // use cache or compute a new expression
    exprCache.get(state.ex) match {
      case Some(eg: (TlaEx, ExprGrade.Value)) =>
        solverContext.log(s"; Using cached value ${eg._1} for expression ${state.ex}")
        coerce(state.setRex(eg._1), state.theory)

      case None =>
        val nextState = doRecursive(0, state)
        exprCache.put(state.ex, nextState.ex) // the grade is not important
        nextState
    }
  }

  /**
    * Rewrite all expressions in a sequence.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite
    * @return a pair (the new state with the original expression, the rewritten expressions)
    */
  def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
    var newState = state // it is easier to write this code with a side effect on the state
    // we should be very careful about propagating arenas here
    def eachExpr(e: TlaEx): TlaEx = {
      val ns = rewriteUntilDone(new SymbState(e, state.theory, newState.arena, newState.binding))
      assert(ns.arena.cellCount >= newState.arena.cellCount)
      newState = ns
      ns.ex
    }

    val rewrittenExprs = es map eachExpr
    (newState.setRex(state.ex).setTheory(state.theory), rewrittenExprs)
  }

  /**
    * An extended version of rewriteSeqUntilDone, where expressions are accompanied with bindings.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite accompanied with bindings
    * @return a pair (the old state in a new context, the rewritten expressions)
    */
  def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
    var newState = state // it is easier to write this code with a side effect on the state
    // we should be very careful about propagating arenas here
    def eachExpr(be: (Binding, TlaEx)): TlaEx = {
      val ns = rewriteUntilDone(new SymbState(be._2, state.theory, newState.arena, be._1))
      assert(ns.arena.cellCount >= newState.arena.cellCount)
      newState = ns
      ns.ex
    }

    val rewrittenExprs = es map eachExpr
    (newState.setRex(state.ex).setTheory(state.theory), rewrittenExprs)
  }

  /**
    * Coerce the state expression from the current theory to another theory.
    *
    * @param state        a symbolic state
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
    strValueCache.push()
    recordDomainCache.push()
    lazyEq.push()
    exprCache.push()
    coercion.push()
    solverContext.push()
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    assert(level > 0)
    intValueCache.pop()
    strValueCache.pop()
    recordDomainCache.pop()
    lazyEq.pop()
    exprCache.pop()
    solverContext.pop()
    coercion.pop()
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
    strValueCache.pop(n)
    recordDomainCache.pop(n)
    lazyEq.pop(n)
    exprCache.pop(n)
    solverContext.pop(n)
    coercion.pop(n)
    level -= n
  }

  /**
    * Clean the context
    */
  override def dispose(): Unit = {
    intValueCache.dispose()
    strValueCache.dispose()
    recordDomainCache.dispose()
    lazyEq.dispose()
    solverContext.dispose()
    coercion.dispose()
  }

  /**
    * Compute a key of a TLA+ expression to quickly decide on a short sequence of rules to try.
    *
    * @param ex a TLA+ expression
    * @return a string that gives us an equivalence class for similar operations (see the code)
    */
  private def key(ex: TlaEx): String = {
    ex match {
      case OperEx(_: TlaUserOper, _*) =>
        "U@"

      case OperEx(oper, _*) =>
        "O@" + oper.name

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

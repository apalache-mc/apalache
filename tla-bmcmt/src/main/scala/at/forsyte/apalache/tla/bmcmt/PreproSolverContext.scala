package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.caches.SimpleCache
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * A preprocessor of the SolverContext that caches all equalities and propagates them
  * before pushing the constraints to the actual solver. This is helpful as our rewriting rules
  * introduce lots of redundant variables that can be easily eliminated by propagation.
  *
  * We use delegation instead of inheritance, as we will integrate with other solvers in the future.
  *
  * Surprisingly, this preprocessor slows down model checking. Figure out, what is going on...
  *
  * @author Igor Konnov
  */
class PreproSolverContext(context: SolverContext) extends SolverContext {
  private val eqCache: SimpleCache[String, TlaEx] = new SimpleCache()

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  override def assertGroundExpr(ex: TlaEx): Unit = {
    // if a variable is equal to a value, we cache this equality
    // and do not propagate it in the solver
    val ppex = preprocess(ex)
    preprocess(ex) match {
      case OperEx(TlaOper.eq, NameEx(name), right) =>
        eqCache.put(name, right)
        context.log(";;    -> pp cache")

      case OperEx(TlaOper.eq, left, NameEx(name)) =>
        eqCache.put(name, left)
        context.log(";;    -> pp cache")

      case _ => // ignore
    }
    context.assertGroundExpr(ppex)
  }

  /**
    * Evaluate a ground TLA+ expression in the current model, which is available after a call to sat().
    * This method assumes that the outcome is either a Boolean or integer.
    * If not, it throws SmtEncodingException.
    *
    * @param ex an expression to evaluate
    * @return a TLA+ value
    */
  override def evalGroundExpr(ex: TlaEx): TlaEx = {
    context.evalGroundExpr(preprocess(ex))
  }

  private def preprocess(ex: TlaEx): TlaEx = {
    ex match {
      case NameEx(name) =>
        eqCache.get(name) match {
          case Some(cached) => cached
          case None => ex
        }

      case OperEx(TlaSetOper.in, _, _) =>
        // do not preprocess these expressions, as we have to find sorts from the names
        ex

      case OperEx(TlaFunOper.app, fun, elem) =>
        // do not preprocess the function, as we have to find sorts from the names
        OperEx(TlaFunOper.app, fun, preprocess(elem))

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args map preprocess :_*)

      case _ => ex
    }
  }


  ////////////////// the rest is just delegation to context



  /**
    * Declare a constant for an arena cell.
    *
    * @param cell a (previously undeclared) cell
    */
  override def declareCell(cell: ArenaCell): Unit = context.declareCell(cell)


  /**
    * Check whether the current view of the SMT solver is consistent with arena.
    *
    * @param arena an arena
    */
  override def checkConsistency(arena: Arena): Unit = context.checkConsistency(arena)

  /**
    * Introduce a new Boolean constant.
    *
    * @return the name of a new constant
    */
  override def introBoolConst(): String = context.introBoolConst()

  /**
    * Get the names of the active Boolean constants (not the cells of type BoolT).
    * This method is used for debugging purposes and may be slow.
    *
    * @return a list of Boolean constant that are active in the current context
    */
  override def getBoolConsts: Iterable[String] = context.getBoolConsts

  /**
    * Get the names of the active integer constants (not the cells of type IntT).
    * This method is used for debugging purposes and may be slow.
    *
    * @return a list of integer constants that are active in the current context
    */
  def getIntConsts: Iterable[String] = context.getIntConsts

  /**
    * Introduce a new integer constant.
    *
    * @return the name of a new constant
    */
  override def introIntConst(): String = context.introIntConst()

  /**
    * Introduce an uninterpreted function associated with a cell.
    *
    * @param domainType a type of the domain
    * @param resultType a type of the result
    * @return the name of the new function (declared in SMT)
    */
  override def declareCellFun(cellName: String, domainType: types.CellT, resultType: types.CellT): Unit =
    context.declareCellFun(cellName, domainType, resultType)

  /**
    * Write a message to the log file. This is helpful to debug the SMT encoding.
    *
    * @param message message text, call-by-name
    */
  override def log(message: => String): Unit = context.log(message)

  /**
    * Is the current context satisfiable?
    *
    * @return true if and only if the context is satisfiable
    */
  override def sat(): Boolean = context.sat()

  /**
    * Get the name of the reserved Boolean constant that is always false
    * (useful to avoid messing with the keywords).
    *
    * @return the name (typically, $B$0)
    */
  override def falseConst: String = context.falseConst

  /**
    * Get the name of the reserved Boolean constant that is always false
    * (useful to avoid messing with the keywords).
    *
    * @return the name (typically, $B$1)
    */
  override def trueConst: String = context.trueConst

  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    context.push()
    eqCache.push()
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    eqCache.pop()
    context.pop()
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n pop n times, if n > 0, otherwise, do nothing
    */
  override def pop(n: Int): Unit = {
    eqCache.pop(n)
    context.pop(n)
  }

  /**
    * Clean the context
    */
  override def dispose(): Unit = {
    eqCache.dispose()
    context.dispose()
  }
}

package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}

/**
  * A cache for integer constants that maps an integer to an integer constant in SMT.
  *
  * @author Igor Konnov
  */
class IntValueCache(solverContext: SolverContext) extends StackableContext {
  /**
    * A context level, see StackableContext
    */
  private var level: Int = 0

  // cache the integer constants that are introduced in SMT for integer literals
  private var cache: Map[BigInt, (String, Int)] = Map()

  def getOrCreate(intValue: Int): String = {
    if (cache.contains(intValue)) {
      cache(intValue)._1
    } else {
      // introduce a new constant
      val intConst = solverContext.introIntConst()
      solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(intValue))))
      cache = cache + (BigInt(intValue) -> (intConst, level))
      intConst
    }
  }

  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    level += 1
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    assert(level > 0)

    def isEntryOlder(mapEntry: (BigInt, (String, Int))): Boolean =
      mapEntry._2._2 < level

    cache = cache filter isEntryOlder
    level -= 1
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n the number of times to call pop
    */
  override def pop(n: Int): Unit = {
    for (_ <- 1.to(n)) {
      pop()
    }
  }

  /**
    * Clean the context.
    */
  override def dispose(): Unit = {
    cache = Map()
    level = 0
  }
}

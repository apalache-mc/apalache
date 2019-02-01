package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, IntT}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Coercion from one theory to another. The coercion results are cached, and thus
  * this class supports StackableContext.
  *
  * As we are assigning sorts to cells now, this class is here just for backward compatibility with the code.
  * It will be removed in the future.
  *
  * @author Igor Konnov
  */
class CoercionWithCache(val stateRewriter: SymbStateRewriter) extends StackableContext {
  type SourceT = (String, Theory)
  type TargetT = String

  /**
    * A context level, see StackableContext
    */
  private var level: Int = 0

  // cache the integer constants that are introduced in SMT for integer literals
  private var cache: Map[SourceT, (TargetT, Int)] = Map()


  def coerce(state: SymbState, targetTheory: Theory): SymbState = {
    // if the expression is a constant, find its theory
    val exTheory =
      if (BoolTheory().hasNameEx(state.ex)) {
        BoolTheory()
      } else if (IntTheory().hasNameEx(state.ex)) {
        IntTheory()
      } else if (CellTheory().hasNameEx(state.ex)) {
        CellTheory()
      } else {
        state.theory // not a constant, assume the state theory
      }

    if (targetTheory == exTheory) {
      // nothing to do
      state.setTheory(targetTheory)
    } else {
      val name = state.ex match {
        case NameEx(n) => n
        case _ => throw new RewriterException("Expected NameEx, found: " + state.ex)
      }

      val cachedValue = cache.get((name, targetTheory))
      if (cachedValue.isDefined) {
        val cachedEx = NameEx(cachedValue.get._1)
        state.setTheory(targetTheory).setRex(cachedEx)
      } else {
        val targetState =
          (exTheory, targetTheory) match {
            case (CellTheory(), BoolTheory()) =>
              cellToBool(state)

            case (CellTheory(), IntTheory()) =>
              cellToInt(state)

            case (BoolTheory(), CellTheory()) =>
              boolToCell(state)

            case (IntTheory(), CellTheory()) =>
              intToCell(state)

            case _ =>
              throw new RewriterException("Coercion from %s to %s is not allowed".format(state.theory, targetTheory))
          }

        val targetName = targetState.ex match {
          case NameEx(n) => n
          case _ => throw new RewriterException("Expected NameEx, found: " + targetState.ex)
        }

        cache = cache + ((name, targetTheory) -> (targetName, level))
        targetState
      }
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

    def isEntryOlder(mapEntry: (SourceT, (TargetT, Int))): Boolean =
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

  private def boolToCell(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if BoolTheory().hasConst(name) =>
        if (name == stateRewriter.solverContext.falseConst) {
          // $B$0 -> $C$0
          state.setRex(state.arena.cellFalse().toNameEx)
            .setTheory(CellTheory())
        } else if (name == stateRewriter.solverContext.trueConst) {
          // $B$1 -> $C$1
          state.setRex(state.arena.cellTrue().toNameEx)
            .setTheory(CellTheory())
        } else {
          // the general case
          val newArena = state.arena.appendCell(BoolT())
          val newCell = newArena.topCell
          // just compare the constants directly, as both of them have type Bool
          val equiv = OperEx(TlaBoolOper.equiv, NameEx(name), newCell.toNameEx)
          stateRewriter.solverContext.assertGroundExpr(equiv)
          state.setArena(newArena)
            .setRex(newCell.toNameEx)
            .setTheory(CellTheory())
        }

      case _ =>
        throw new InvalidTlaExException("Expected a Boolean predicate, found: " + state.ex, state.ex)
    }
  }

  private def cellToBool(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if CellTheory().hasConst(name) =>
        if (name == state.arena.cellFalse().toString) {
          // $C$0 -> $B$0
          state.setRex(NameEx(stateRewriter.solverContext.falseConst))
            .setTheory(BoolTheory())
        } else if (name == state.arena.cellTrue().toString) {
          // $C$1 -> $B$1
          state.setRex(NameEx(stateRewriter.solverContext.trueConst))
            .setTheory(BoolTheory())
        } else {
          // general case
          val pred = stateRewriter.solverContext.introBoolConst()
          // just compare the constants directly, as both of them have type Bool
          val equiv = OperEx(TlaBoolOper.equiv, NameEx(pred), NameEx(name))
          stateRewriter.solverContext.assertGroundExpr(equiv)
          state.setRex(NameEx(pred)).setTheory(BoolTheory())
        }

      case _ =>
        throw new InvalidTlaExException("Expected a cell, found: " + state.ex, state.ex)
    }
  }

  private def intToCell(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if IntTheory().hasConst(name) =>
        val newArena = state.arena.appendCell(IntT())
        val newCell = newArena.topCell
        val equiv = OperEx(TlaOper.eq, NameEx(name), newCell.toNameEx)
        stateRewriter.solverContext.assertGroundExpr(equiv)
        state.setArena(newArena)
          .setRex(newCell.toNameEx)
          .setTheory(CellTheory())

      case _ =>
        throw new InvalidTlaExException("Expected an integer predicate, found: " + state.ex, state.ex)
    }
  }

  private def cellToInt(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if CellTheory().hasConst(name) =>
        val intConst = stateRewriter.solverContext.introIntConst()
        val equiv = OperEx(TlaOper.eq, NameEx(name), NameEx(intConst))
        stateRewriter.solverContext.assertGroundExpr(equiv)
        state.setRex(NameEx(intConst))
          .setTheory(IntTheory())

      case _ =>
        throw new InvalidTlaExException("Expected an integer predicate, found: " + state.ex, state.ex)
    }
  }
}

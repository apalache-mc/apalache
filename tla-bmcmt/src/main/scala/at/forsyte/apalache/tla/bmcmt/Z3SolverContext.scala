package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import com.microsoft.z3._

/**
  * An implementation of a SolverContext with Z3.
  *
  * @author Igor Konnov
  */
class Z3SolverContext extends SolverContext {
  var level: Int = 0
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()
  private val cellSort: UninterpretedSort = z3context.mkUninterpretedSort("Cell")

  /**
    * Dispose whatever has to be disposed in the end.
    */
  override def dispose(): Unit = {
    z3context.close()
  }

  /**
    * Declare a constant for an arena cell.
    *
    * @param cell a (previously undeclared) cell
    */
  override def declareCell(cell: ArenaCell): Unit = {
    z3context.mkConstDecl(cell.toString, cellSort)
  }

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  def assertCellExpr(ex: TlaEx): Unit = {
    z3solver.add(toBoolExpr(ex).asInstanceOf[BoolExpr])
  }


  /**
    * Push SMT context
    */
  override def push(): Unit = {
    z3solver.push()
    level += 1
  }

  /**
    * Pop SMT context
    */
  override def pop(): Unit = {
    if (level > 0) {
      z3solver.pop()
      level -= 1
    }
  }

  override def popTo(newLevel: Int): Unit = {
    if (level > newLevel) {
      z3solver.pop(level - newLevel)
      level = newLevel
    }
  }

  override def sat(): Boolean = {
    z3solver.check() == Status.SATISFIABLE
  }

  private def toBoolExpr(ex: TlaEx): Expr = {
    ex match {
      case NameEx(name) =>
        if (!isCellName(name)) {
          throw new InvalidTlaExException("Expected a cell, found name: " + name, ex)
        }
        z3context.mkConst(name, cellSort)

      case OperEx(TlaOper.eq, lhs, rhs) =>
        z3context.mkEq(toBoolExpr(lhs), toBoolExpr(rhs))

      case OperEx(TlaOper.ne, lhs, rhs) =>
        z3context.mkNot(z3context.mkEq(toBoolExpr(lhs), toBoolExpr(rhs)))

      case OperEx(TlaBoolOper.and, es@_*) =>
        val newEs = es.map(e => toBoolExpr(e).asInstanceOf[BoolExpr])
        z3context.mkAnd(newEs: _*)

      case OperEx(TlaBoolOper.or, es@_*) =>
        val newEs = es.map(e => toBoolExpr(e).asInstanceOf[BoolExpr])
        z3context.mkOr(newEs: _*)

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        val lhsZ3 = toBoolExpr(lhs).asInstanceOf[BoolExpr]
        val rhsZ3 = toBoolExpr(rhs).asInstanceOf[BoolExpr]
        z3context.mkImplies(lhsZ3, rhsZ3)

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        val lhsZ3 = toBoolExpr(lhs).asInstanceOf[BoolExpr]
        val rhsZ3 = toBoolExpr(rhs).asInstanceOf[BoolExpr]
        z3context.mkEq(lhsZ3, rhsZ3)

      case _ =>
        throw new InvalidTlaExException("Unexpected TLA+ expression", ex)
    }
  }
}

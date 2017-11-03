package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import com.microsoft.z3._

/**
  * An implementation of a SolverContext using Z3.
  *
  * @author Igor Konnov
  */
class Z3SolverContext extends SolverContext {
  var level: Int = 0
  var nBoolConsts: Int = 0
  var nIntConsts: Int = 0
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()
  private val cellSort: UninterpretedSort = z3context.mkUninterpretedSort("Cell")
  /**
    * Uninterpreted predicate in(c, d) that expresses whether c is a member of d.
    */
  private val inFun: FuncDecl =
    z3context.mkFuncDecl("in", Array[Sort](cellSort, cellSort), z3context.getBoolSort)
  private val valIntFun: FuncDecl =
    z3context.mkFuncDecl("valInt", cellSort, z3context.getIntSort)

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
    z3solver.add(toExpr(ex).asInstanceOf[BoolExpr])
  }


  /**
    * Introduce a new Boolean constant.
    *
    * @return the name of a new constant
    */
  override def introBoolConst(): String = {
    val name = "%s%d".format(BoolTheory().namePrefix, nBoolConsts)
    nBoolConsts += 1
    name
  }

  /**
    * Introduce a new integer constant.
    *
    * @return the name of a new constant
    */
  override def introIntConst(): String = {
    val name = "%s%d".format(IntTheory().namePrefix, nIntConsts)
    nIntConsts += 1
    name
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

  /**
    * Print the collected constraints in the SMTLIB2 format using Z3 API.
    *
    * @return a long string of statements in SMTLIB2 format as provided by Z3
    */
  def toSmtlib2: String = {
    z3solver.toString
  }

  private def toExpr(ex: TlaEx): Expr = {
    ex match {
      case NameEx(name) =>
        if (CellTheory().hasConst(name)) {
          z3context.mkConst(name, cellSort)
        } else if (BoolTheory().hasConst(name)) {
          z3context.mkBoolConst(name)
        } else if (IntTheory().hasConst(name)) {
          z3context.mkIntConst(name)
        } else {
          throw new InvalidTlaExException("Expected a cell, found name: " + name, ex)
        }

      case ValEx(TlaFalse) =>
        z3context.mkFalse()

      case ValEx(TlaTrue) =>
        z3context.mkTrue()

      case ValEx(TlaInt(num)) =>
        if (num.isValidLong) {
          z3context.mkInt(num.toLong)
        } else {
          throw new SmtEncodingException("A number constant is too large to fit in Long: " + num)
        }

      case OperEx(TlaOper.eq, lhs@NameEx(lname), rhs@NameEx(rname)) =>
        if (CellTheory().hasConst(lname) && CellTheory().hasConst(rname)) {
          // just comparing cells
          z3context.mkEq(z3context.mkConst(lname, cellSort), z3context.mkConst(rname, cellSort))
        } else {
          // comparing integers and Boolean to cells, Booleans to Booleans, and Integers to Integers
          toEqExpr(lhs, rhs, toExpr(lhs), toExpr(rhs))
        }

      case OperEx(TlaOper.eq, lhs, rhs) =>
        toEqExpr(lhs, rhs, toExpr(lhs), toExpr(rhs))

      case OperEx(TlaOper.ne, lhs, rhs) =>
        z3context.mkNot(toExpr(OperEx(TlaOper.eq, lhs, rhs)).asInstanceOf[BoolExpr])

      case OperEx(TlaBoolOper.and, es@_*) =>
        val newEs = es.map(e => toExpr(e).asInstanceOf[BoolExpr])
        z3context.mkAnd(newEs: _*)

      case OperEx(TlaBoolOper.or, es@_*) =>
        val newEs = es.map(e => toExpr(e).asInstanceOf[BoolExpr])
        z3context.mkOr(newEs: _*)

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        val lhsZ3 = toExpr(lhs).asInstanceOf[BoolExpr]
        val rhsZ3 = toExpr(rhs).asInstanceOf[BoolExpr]
        z3context.mkImplies(lhsZ3, rhsZ3)

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        val lhsZ3 = toExpr(lhs).asInstanceOf[BoolExpr]
        val rhsZ3 = toExpr(rhs).asInstanceOf[BoolExpr]
        z3context.mkEq(lhsZ3, rhsZ3)

      case OperEx(TlaBoolOper.not, e) =>
        val exZ3 = toExpr(e).asInstanceOf[BoolExpr]
        z3context.mkNot(exZ3)

      case OperEx(TlaSetOper.in, NameEx(elemName), NameEx(setName)) =>
        val elem = z3context.mkConst(elemName, cellSort)
        val set = z3context.mkConst(setName, cellSort)
        z3context.mkApp(inFun, elem, set)

      case _ =>
        throw new InvalidTlaExException("Unexpected TLA+ expression: " + ex, ex)
    }
  }

  private def toEqExpr(lhs: TlaEx, rhs: TlaEx, le: Expr, re: Expr) = {
    (le, re) match {
      case (_: BoolExpr, _: BoolExpr)
           | (_: IntExpr, _: IntExpr) =>
        z3context.mkEq(toExpr(lhs), toExpr(rhs))

      case (_: IntExpr, _: Expr) =>
        // comparing an integer constant and a value
        z3context.mkEq(le, z3context.mkApp(valIntFun, re))

      case (_: Expr, _: IntExpr) =>
        // comparing an integer constant and a value
        z3context.mkEq(z3context.mkApp(valIntFun, le), re)

      case _ =>
        throw new CheckerException("Incomparable expressions")
    }
  }
}

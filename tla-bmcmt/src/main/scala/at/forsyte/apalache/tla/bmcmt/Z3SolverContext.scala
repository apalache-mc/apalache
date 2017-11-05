package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import com.microsoft.z3._

import scala.collection.mutable

/**
  * An implementation of a SolverContext using Z3.
  *
  * @author Igor Konnov
  */
class Z3SolverContext extends SolverContext {
  var level: Int = 0
  var nBoolConsts: Int = 3 // the first three cells are reserved for: false, true, fail
  var nIntConsts: Int = 0
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()
  private val cellSort: UninterpretedSort = z3context.mkUninterpretedSort("Cell")
  /**
    * Uninterpreted predicate in(c, d) that expresses whether c is a member of d.
    */
  private val inFun: FuncDecl =
    z3context.mkFuncDecl("in", Array[Sort](cellSort, cellSort), z3context.getBoolSort)
  /**
    * Uninterpreted function to store integer values of integer cells.
    */
  private val valIntFun: FuncDecl =
    z3context.mkFuncDecl("valInt", cellSort, z3context.getIntSort)
  /**
    * Uninterpreted functions C -> C associated with function cells.
    */
  private val cellFuns: mutable.Map[String, FuncDecl] = new mutable.HashMap[String, FuncDecl]()


  def falseConst: String = BoolTheory().namePrefix + "0" // $B$0
  def trueConst: String = BoolTheory().namePrefix + "1" // $B$1
  // this constant should equal true, when a failure occured
  def failConst: String = BoolTheory().namePrefix + "2" // $B$2
  assertGroundExpr(NameEx(trueConst))
  assertGroundExpr(OperEx(TlaBoolOper.not, NameEx(falseConst)))

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
  def assertGroundExpr(ex: TlaEx): Unit = {
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
    * Introduce an uninterpreted function associated with a cell.
    *
    * @param cell an arena cell
    * @return a function declaration (also stored in the context)
    */
  def getOrIntroCellFun(cell: ArenaCell): FuncDecl = {
    val cellName = cell.toString
    cellFuns.get(cellName) match {
      case Some(funDecl) =>
        funDecl

      case None =>
        val name = "fun%d".format(cell.id)
        val funDecl = z3context.mkFuncDecl(name, cellSort, cellSort)
        cellFuns.put(cellName, funDecl)
        funDecl
    }
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

      case OperEx(oper: TlaArithOper, lex, rex) =>
        // convert to an arithmetic expression
        toArithExpr(ex)

      case OperEx(TlaOper.eq, lhs@NameEx(lname), rhs@NameEx(rname)) =>
        if (CellTheory().hasConst(lname) && CellTheory().hasConst(rname)) {
          // just comparing cells
          z3context.mkEq(z3context.mkConst(lname, cellSort), z3context.mkConst(rname, cellSort))
        } else {
          // comparing integers and Boolean to cells, Booleans to Booleans, and Integers to Integers
          toEqExpr(toExpr(lhs), toExpr(rhs))
        }

      case OperEx(TlaOper.eq, lhs, rhs) =>
        toEqExpr(toExpr(lhs), toExpr(rhs))

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

      case OperEx(TlaFunOper.app, NameEx(funName), NameEx(argName)) =>
        // apply the function associated with a cell
        val fun = cellFuns.apply(funName)
        val arg = z3context.mkConst(argName, cellSort)
        z3context.mkApp(fun, arg)

      case _ =>
        throw new InvalidTlaExException("Unexpected TLA+ expression: " + ex, ex)
    }
  }

  private def toEqExpr(le: Expr, re: Expr) = {
    (le, re) match {
      case (_: BoolExpr, _: BoolExpr)
           | (_: IntExpr, _: IntExpr) =>
        z3context.mkEq(le, re)

      case (_: IntExpr, _: Expr) =>
        // comparing an integer constant and a value
        z3context.mkEq(le, z3context.mkApp(valIntFun, re))

      case (_: Expr, _: IntExpr) =>
        // comparing an integer constant and a value
        z3context.mkEq(z3context.mkApp(valIntFun, le), re)

      case (_: Expr, _: Expr) =>
        // comparing a cell constant against a function application
        z3context.mkEq(le, re)

      case _ =>
        throw new CheckerException("Incomparable expressions")
    }
  }

  private def toArithExpr(ex: TlaEx): Expr = {
    ex match {
      case NameEx(name) if IntTheory().hasConst(name) =>
        z3context.mkIntConst(name)

      case OperEx(TlaArithOper.lt, left, right) =>
        z3context.mkLt(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.le, left, right) =>
        z3context.mkLe(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.gt, left, right) =>
        z3context.mkGt(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.ge, left, right) =>
        z3context.mkGe(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.plus, left, right) =>
        z3context.mkAdd(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.minus, left, right) =>
        z3context.mkSub(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.mult, left, right) =>
        z3context.mkMul(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.div, left, right) =>
        z3context.mkDiv(toArithExpr(left).asInstanceOf[ArithExpr],
          toArithExpr(right).asInstanceOf[ArithExpr])

      case OperEx(TlaArithOper.mod, left, right) =>
        z3context.mkMod(toArithExpr(left).asInstanceOf[IntExpr],
          toArithExpr(right).asInstanceOf[IntExpr])

      case _ =>
        throw new InvalidTlaExException("Unexpected arithmetic expression: " + ex, ex)
    }
  }
}

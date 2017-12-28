package at.forsyte.apalache.tla.bmcmt

import java.io.{File, PrintWriter}

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_lbool

import scala.collection.mutable

/**
  * An implementation of a SolverContext using Z3.
  *
  * @author Igor Konnov
  */
class Z3SolverContext(debug: Boolean = false) extends SolverContext {
  /**
    * A log writer, for debugging purposes.
    */
  private val logWriter: PrintWriter = initLog()

  var level: Int = 0
  var nBoolConsts: Int = 3 // the first three cells are reserved for: false, true, fail
  var nIntConsts: Int = 0
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()

  private val cellSort: UninterpretedSort = z3context.mkUninterpretedSort("Cell")
  // log declaration, so we can directly replay the log with z3 -smt2
  log("(declare-sort Cell 0)")

  /**
    * Uninterpreted predicate in(c, d) that expresses whether c is a member of d.
    */
  private val inFun: FuncDecl =
    z3context.mkFuncDecl("in", Array[Sort](cellSort, cellSort), z3context.getBoolSort)
  log("(declare-fun in (Cell Cell) Bool)") // log declaration

  /**
    * Uninterpreted function to store integer values of integer cells.
    */
  private val valIntFun: FuncDecl =
    z3context.mkFuncDecl("valInt", cellSort, z3context.getIntSort)
  log("(declare-fun valInt (Cell) Int)") // log declaration

  /**
    * The calls to z3context.mkConst consume 20% of the running time, according to VisualVM.
    * Let's cache the constants, if Z3 cannot do it well.
    * Again, the cache carries the context level, to support push and pop.
    */
  private val constCache: mutable.Map[String, (Expr, Int)] =
    new mutable.HashMap[String, (Expr, Int)]

  /**
    * Uninterpreted functions C -> C associated with function cells.
    * Since context operations may clear function declaration,
    * we carry the context level in the map and clean the function declarations on pop.
    */
  private val cellFuns: mutable.Map[String, (FuncDecl, Int)] =
    new mutable.HashMap[String, (FuncDecl, Int)]()

  def falseConst: String = introBoolConst() // $B$0
  def trueConst: String = introBoolConst() // $B$1

  // this constant should equal true, when a failure occured, TODO: figure out the failure semantics
  def failConst: String = introBoolConst() // $B$2
  assertGroundExpr(NameEx(trueConst))
  assertGroundExpr(OperEx(TlaBoolOper.not, NameEx(falseConst)))

  /**
    * Sometimes, we lose a fresh arena in the rewriting rules. As this situation is very hard to debug,
    * we are tracking here the largest cell id per SMT context. If the user is trying to add a cell
    * with a smaller id, there is a good chance that a fresher arena was overwritten with an older one.
    * To find bugs as soon as possible, we crash immediately.
    */
  private var maxCellIdPerContext = List(-1)

  /**
    * Dispose whatever has to be disposed in the end.
    */
  override def dispose(): Unit = {
    z3context.close()
    logWriter.close()
  }

  /**
    * Declare a constant for an arena cell.
    *
    * @param cell a (previously undeclared) cell
    */
  override def declareCell(cell: ArenaCell): Unit = {
    log(s";; declare cell($cell): ${cell.cellType}")
    log(s"(declare-const $cell Cell)")
    if (maxCellIdPerContext.head >= cell.id) {
      // Checking consistency. When the user accidentally replaces a fresh arena with an older one,
      // we report it immediately. Otherwise, it is very hard to find the cause.
      logWriter.flush() // flush the SMT log
      throw new InternalCheckerError("Declaring cell %d, while cell %d has been already declared. Damaged arena?"
        .format(cell.id, maxCellIdPerContext.head))
    } else {
      maxCellIdPerContext = cell.id +: maxCellIdPerContext.tail
    }
    val cellName = cell.toString
    z3context.mkConstDecl(cellName, cellSort)
    val const = z3context.mkConst(cellName, cellSort)
    constCache += (cellName -> (const, level))
  }

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  def assertGroundExpr(ex: TlaEx): Unit = {
    log(s";; assert ${UTFPrinter.apply(ex)}")
    val z3expr = toExpr(ex)
    log(s"(assert ${z3expr.toString})")
    z3solver.add(z3expr.asInstanceOf[BoolExpr])
  }

  /**
    * Evaluate a ground TLA+ expression in the current model, which is available after a call to sat().
    * This method assumes that the outcome is one of the basic types: a Boolean, integer, or a cell constant.
    * If not, it throws SmtEncodingException.
    *
    * @param ex an expression to evaluate
    * @return a TLA+ value
    */
  def evalGroundExpr(ex: TlaEx): TlaEx = {
    val z3expr = z3solver.getModel.eval(toExpr(ex), true)
    z3expr match {
      case b: BoolExpr =>
        val isTrue = b.getBoolValue.equals(Z3_lbool.Z3_L_TRUE)
        ValEx(if (isTrue) TlaTrue else TlaFalse) // in undefined case, just return false

      case i: IntNum =>
        ValEx(TlaInt(i.getBigInteger))

      case _ =>
        if (z3expr.isConst && z3expr.getSort == cellSort) {
          NameEx(z3expr.toString)
        } else {
          throw new SmtEncodingException("Expected an integer or Boolean, found: " + z3expr)
        }
    }
  }

  private def initLog(): PrintWriter = {
    val writer = new PrintWriter(new File("log.smt"))
    if (!debug) {
      writer.println("Logging is disabled (Z3SolverContext.debug = false). Activate with --debug.")
      writer.flush()
    }
    writer
  }

  /**
    * Log message to the logging file. This is helpful to debug the SMT encoding.
    *
    * @param message message text, called by name, so evaluated only when needed
    */
  def log(message: => String): Unit = {
    if (debug) {
      logWriter.println(message)
    }
  }

  /**
    * Introduce a new Boolean constant.
    *
    * @return the name of a new constant
    */
  override def introBoolConst(): String = {
    val name = "%s%d".format(BoolTheory().namePrefix, nBoolConsts)
    log(s";; declare bool $name")
    log(s"(declare-const $name Bool)")
    nBoolConsts += 1
    val const = z3context.mkConst(name, z3context.getBoolSort)
    constCache += (name -> (const, level))
    name
  }

  /**
    * Introduce a new integer constant.
    *
    * @return the name of a new constant
    */
  override def introIntConst(): String = {
    val name = "%s%d".format(IntTheory().namePrefix, nIntConsts)
    log(";; declare int $name")
    log("(declare-const $name Int)")
    nIntConsts += 1
    val const = z3context.mkConst(name, z3context.getIntSort)
    constCache += (name -> (const, level))
    name
  }

  /**
    * Introduce an uninterpreted function associated with a cell.
    *
    * @param cell an arena cell
    * @return the name of the new function (declared in SMT)
    */
  def getOrIntroCellFun(cell: ArenaCell): String = {
    val cellName = cell.toString
    cellFuns.get(cellName) match {
      case Some((funDecl, _)) =>
        funDecl.getName.toString

      case None =>
        val name = "fun%d".format(cell.id)
        log(s";; declare cell fun $name")
        log(s"(declare-fun $name (Cell) Cell)")
        val funDecl = z3context.mkFuncDecl(name, cellSort, cellSort)
        cellFuns.put(cellName, (funDecl, level))
        name
    }
  }

  /**
    * Push SMT context
    */
  override def push(): Unit = {
    log("(push)")
    logWriter.flush() // good time to flush
    z3solver.push()
    maxCellIdPerContext = maxCellIdPerContext.head +: maxCellIdPerContext
    level += 1
  }

  /**
    * Pop SMT context
    */
  override def pop(): Unit = {
    if (level > 0) {
      log("(pop)")
      logWriter.flush() // good time to flush
      z3solver.pop()
      maxCellIdPerContext = maxCellIdPerContext.tail
      level -= 1
      // clean the caches
      cellFuns.retain((_, value) => value._2 <= level)
      constCache.retain((_, value) => value._2 <= level)
    }
  }

  override def pop(n: Int): Unit = {
    if (n > 0) {
      log("(pop $n)")
      logWriter.flush() // good time to flush
      z3solver.pop(n)
      maxCellIdPerContext = maxCellIdPerContext.drop(n)
      level -= n
      // clean the caches
      cellFuns.retain((_, value) => value._2 <= level)
      constCache.retain((_, value) => value._2 <= level)
    }
  }

  override def sat(): Boolean = {
    log("(check-sat)")
    val status = z3solver.check()
    log(s";; sat = ${status == Status.SATISFIABLE}")
    logWriter.flush() // good time to flush
    if (status == Status.UNKNOWN) {
      // that seems to be the only reasonable behavior
      throw new SmtEncodingException("SMT solver reports UNKNOWN. Perhaps, your specification is outside the supported logic.")
    }
    status == Status.SATISFIABLE
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
        constCache(name)._1 // the cached expression

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
          z3context.mkEq(constCache(lname)._1, constCache(rname)._1)
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
        val elem = constCache(elemName)._1
        val set = constCache(setName)._1
        z3context.mkApp(inFun, elem, set)

      case OperEx(TlaFunOper.app, NameEx(funName), NameEx(argName)) =>
        // apply the function associated with a cell
        val arg = constCache(argName)._1
        if (funName != "$$intVal") {
          val (fun, _) = cellFuns(funName)
          z3context.mkApp(fun, arg)
        } else {
          // a hack to get back the integer values from a model
          z3context.mkApp(valIntFun, arg)
        }

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

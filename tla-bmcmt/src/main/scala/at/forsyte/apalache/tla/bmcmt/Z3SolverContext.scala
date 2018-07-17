package at.forsyte.apalache.tla.bmcmt

import java.io.{File, PrintWriter}

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT, FailPredT, IntT}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, _}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaFalse, TlaInt, TlaTrue}
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
  var nBoolConsts: Int = 0 // the first three cells are reserved for: false and true
  var nIntConsts: Int = 0
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()
  private val simplifier = new ConstSimplifier()

  /**
    * Caching one uninterpreted sort for each cell signature. For integers, the integer sort.
    */
  private val cellSorts: mutable.Map[String, (Sort, Int)] =
    new mutable.HashMap[String, (Sort, Int)]

  /**
    * Uninterpreted functions C -> C associated with function cells.
    * Since context operations may clear function declaration,
    * we carry the context level in the map and clean the function declarations on pop.
    */
  private val funDecls: mutable.Map[String, (FuncDecl, Int)] =
    new mutable.HashMap[String, (FuncDecl, Int)]()

  /**
    * The calls to z3context.mkConst consume 20% of the running time, according to VisualVM.
    * Let's cache the constants, if Z3 cannot do it well.
    * Again, the cache carries the context level, to support push and pop.
    */
  private val constCache: mutable.Map[String, (Expr, CellT, Int)] =
    new mutable.HashMap[String, (Expr, CellT, Int)]

  val falseConst: String = introBoolConst() // $B$0, for simplicity
  val trueConst: String = introBoolConst() // $B$1, for simplicity
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
    constCache.clear()
    funDecls.clear()
    cellSorts.clear()
  }

  /**
    * Declare a constant for an arena cell.
    *
    * @param cell a (previously undeclared) cell
    */
  override def declareCell(cell: ArenaCell): Unit = {
    if (maxCellIdPerContext.head >= cell.id) {
      // Checking consistency. When the user accidentally replaces a fresh arena with an older one,
      // we report it immediately. Otherwise, it is very hard to find the cause.
      logWriter.flush() // flush the SMT log
      throw new InternalCheckerError("Declaring cell %d, while cell %d has been already declared. Damaged arena?"
        .format(cell.id, maxCellIdPerContext.head))
    } else {
      maxCellIdPerContext = cell.id +: maxCellIdPerContext.tail
    }

    log(s";; declare cell($cell): ${cell.cellType}")
    val cellSort = getOrMkCellSort(cell.cellType)
    log(s"(declare-const $cell $cellSort)")
    val cellName = cell.toString
    z3context.mkConstDecl(cellName, cellSort)
    val const = z3context.mkConst(cellName, cellSort)
    constCache += (cellName -> (const, cell.cellType, level))

    if (cell.id <= 1) {
      // Either FALSE or TRUE. Enforce its value explicitely
      val expr =
        if (cell.id == 0) OperEx(TlaBoolOper.not, NameEx(cellName))
        else NameEx(cellName)
      assertGroundExpr(expr)
    }
  }

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  def assertGroundExpr(ex: TlaEx): Unit = {
    log(s";; assert ${UTFPrinter.apply(ex)}")
    val z3expr = toExpr(simplifier.simplify(ex))
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
    val z3expr = z3solver.getModel.eval(toExpr(simplifier.simplify(ex)), true)
    z3expr match {
      case b: BoolExpr =>
        val isTrue = b.getBoolValue.equals(Z3_lbool.Z3_L_TRUE)
        ValEx(if (isTrue) TlaTrue else TlaFalse) // in undefined case, just return false

      case i: IntNum =>
        ValEx(TlaInt(i.getBigInteger))

      case _ =>
        if (z3expr.isConst && z3expr.getSort.getName.toString.startsWith("Cell_")) {
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
    constCache += (name -> (const, BoolT(), level))
    name
  }


  /**
    * Get the names of the active Boolean constants (not the cells of type BoolT).
    * This method is used for debugging purposes and may be slow.
    *
    * @return a list of Boolean constant that are active in the current context
    */
  override def getBoolConsts(): Iterable[String] = {
    val boolTheory = BoolTheory()
    constCache.keys filter boolTheory.hasConst
  }

  /**
    * Introduce a new integer constant.
    *
    * @return the name of a new constant
    */
  override def introIntConst(): String = {
    val name = "%s%d".format(IntTheory().namePrefix, nIntConsts)
    log(s";; declare int $name")
    log(s"(declare-const $name Int)")
    nIntConsts += 1
    val const = z3context.mkConst(name, z3context.getIntSort)
    constCache += (name -> (const, IntT(), level))
    name
  }

  /**
    * Introduce an uninterpreted function associated with a cell.
    *
    * @param argType    an argument type
    * @param resultType a result type
    * @return the name of the new function (declared in SMT)
    */
  def declareCellFun(cellName: String, argType: CellT, resultType: CellT): Unit = {
    val domSig = argType.signature
    val resSig = resultType.signature
    val funName = s"fun$cellName"
    if (funDecls.contains(funName)) {
      throw new SmtEncodingException(s"Declaring twice the function associated with cell $cellName")
    } else {
      val domSort = getOrMkCellSort(argType)
      val cdmSort = getOrMkCellSort(resultType)
      log(s";; declare cell fun $funName")
      log(s"(declare-fun $funName ($domSort) $cdmSort)")
      val funDecl = z3context.mkFuncDecl(funName, domSort, cdmSort)
      funDecls += (funName -> (funDecl, level))
    }
  }

  private def getCellFun(cellName: String): FuncDecl = {
    val funName = s"fun$cellName"
    val funDecl = funDecls.get(funName)
    if (funDecl.isDefined) {
      funDecl.get._1
    } else {
      throw new SmtEncodingException(s"A function associated with cell $cellName is not declared")
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
      cellSorts.retain((_, value) => value._2 <= level)
      funDecls.retain((_, value) => value._2 <= level)
      constCache.retain((_, value) => value._3 <= level)
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
      cellSorts.retain((_, value) => value._2 <= level)
      funDecls.retain((_, value) => value._2 <= level)
      constCache.retain((_, value) => value._3 <= level)
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

  private def getOrMkCellSort(cellType: CellT): Sort = {
    val sig = "Cell_" + cellType.signature
    val sort = cellSorts.get(sig)
    if (sort.isDefined) {
      sort.get._1
    } else {
      val newSort =
        cellType match {
          case BoolT() =>
            z3context.getBoolSort

          case IntT() =>
            z3context.getIntSort

          case FailPredT() =>
            z3context.getBoolSort

          case _ =>
            log(s"(declare-sort $sig 0)")
            z3context.mkUninterpretedSort(sig)
        }

      cellSorts += (sig -> (newSort, level))
      newSort
    }
  }

  private def getOrMkInPred(setType: CellT, elemType: CellT): FuncDecl = {
    val name = s"in_${elemType.signature}_${setType.signature}"
    val funDecl = funDecls.get(name)
    if (funDecl.isDefined) {
      funDecl.get._1
    } else {
      val elemSort = getOrMkCellSort(elemType)
      val setSort = getOrMkCellSort(setType)
      val newDecl = z3context.mkFuncDecl(name,
        Array[Sort](elemSort, setSort), z3context.getBoolSort)
      funDecls += (name -> (newDecl, level))
      log(s"(declare-fun $name ($elemSort $setSort) Bool)") // log declaration
      newDecl
    }
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

      case OperEx(oper: TlaArithOper, subex) =>
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
        val mapped_es = es map toExpr
        // check the assertion before casting, to make debugging easier
        assert(mapped_es.forall(e => e.isInstanceOf[BoolExpr]))
        val cast_es = mapped_es.map(_.asInstanceOf[BoolExpr])
        z3context.mkOr(cast_es: _*)

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        val lhsZ3 = toExpr(lhs).asInstanceOf[BoolExpr]
        val rhsZ3 = toExpr(rhs).asInstanceOf[BoolExpr]
        z3context.mkImplies(lhsZ3, rhsZ3)

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        val lhsZ3 = toExpr(lhs).asInstanceOf[BoolExpr]
        val rhsZ3 = toExpr(rhs).asInstanceOf[BoolExpr]
        z3context.mkEq(lhsZ3, rhsZ3)

      case OperEx(TlaControlOper.ifThenElse, cond, thenExpr, elseExpr) =>
        val boolCond = toExpr(cond).asInstanceOf[BoolExpr]
        val thenZ3 = toExpr(thenExpr)
        val elseZ3 = toExpr(elseExpr)
        z3context.mkITE(boolCond, thenZ3, elseZ3)

      case OperEx(TlaBoolOper.not, e) =>
        val exZ3 = toExpr(e).asInstanceOf[BoolExpr]
        z3context.mkNot(exZ3)

      case OperEx(TlaSetOper.in, NameEx(elemName), NameEx(setName)) =>
        val elemEntry = constCache(elemName)
        val setEntry = constCache(setName)
        val inFun = getOrMkInPred(setEntry._2, elemEntry._2)
        z3context.mkApp(inFun, elemEntry._1, setEntry._1)

      case OperEx(TlaSetOper.in, arg @ ValEx(TlaInt(_)), NameEx(setName)) =>
        val setEntry = constCache(setName)
        val inFun = getOrMkInPred(setEntry._2, IntT())
        z3context.mkApp(inFun, toExpr(arg), setEntry._1)

      case OperEx(TlaSetOper.in, arg @ ValEx(TlaBool(_)), NameEx(setName)) =>
        val setEntry = constCache(setName)
        val inFun = getOrMkInPred(setEntry._2, BoolT())
        z3context.mkApp(inFun, toExpr(arg), setEntry._1)

      case OperEx(TlaSetOper.notin, elem, set) =>
        z3context.mkNot(toExpr(OperEx(TlaSetOper.in, elem, set)).asInstanceOf[BoolExpr])

      case OperEx(TlaFunOper.app, NameEx(funName), NameEx(argName)) =>
        // apply the function associated with a cell
        val arg = constCache(argName)._1
        z3context.mkApp(getCellFun(funName), arg)

      case OperEx(TlaFunOper.app, NameEx(funName), arg) =>
        // apply the function associated with a cell
        z3context.mkApp(getCellFun(funName), toExpr(arg))

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
        // comparing an integer constant and a cell of integer type, which is declared as integer
        z3context.mkEq(le, re)

      case (_: Expr, _: IntExpr) =>
        // comparing an integer constant and a cell of integer type, which is declared as integer
        z3context.mkEq(le, re)

      case (_: Expr, _: Expr) =>
        // comparing a cell constant against a function application
        z3context.mkEq(le, re)

      case _ =>
        throw new CheckerException("Incomparable expressions")
    }
  }

  private def toArithExpr(ex: TlaEx): Expr = {
    ex match {
      case ValEx(TlaInt(num)) =>
        if (num.isValidLong) {
          z3context.mkInt(num.toLong)
        } else {
          throw new SmtEncodingException("A number constant is too large to fit in Long: " + num)
        }

      case NameEx(name) =>
        z3context.mkIntConst(name) // TODO: incompatible sorts?

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

      case OperEx(TlaArithOper.uminus, subex) =>
        z3context.mkUnaryMinus(toArithExpr(subex).asInstanceOf[IntExpr])

      case _ =>
        throw new InvalidTlaExException("Unexpected arithmetic expression: " + ex, ex)
    }
  }
}

package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.io.OutputManager

import java.io.{File, PrintWriter}
import java.util.concurrent.atomic.AtomicLong
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.profiler.{IdleSmtListener, SmtListener}
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT, IntT}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.UTFPrinter
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_lbool
import org.apache.commons.io.output.NullOutputStream

import scala.collection.mutable

/**
 * <p>
 * An implementation of a SolverContext using Z3. Note that this class overrides the global z3 settings
 * `sat.random_seed`, `smt.random_seed`, `fp.spacer.random_seed`, and `sls.random_seed` with `config.randomSeed`.
 * Although it is usually not a good idea to override the global settings, we do it to isolate the code
 * specific to z3 in this class.
 * </p>
 *
 * @author Igor Konnov
 */
class Z3SolverContext(val config: SolverConfig) extends SolverContext {
  private val id: Long = Z3SolverContext.createId()

  /**
   * A log writer, for debugging purposes.
   */
  private val logWriter: PrintWriter = initLog()

  // dump the configuration parameters in the log
  // set the global configuration parameters for z3 modules
  Z3SolverContext.RANDOM_SEED_PARAMS.foreach { p =>
    Global.setParameter(p, config.randomSeed.toString)
    logWriter.println(";; %s = %s".format(p, config.randomSeed))
  //    the following fails with an exception: java.lang.NoSuchFieldError: value
  //      logWriter.println(";; %s = %s".format(p, Global.getParameter(p)))
  }

  var level: Int = 0
  var nBoolConsts: Int = 0 // the solver introduces Boolean constants internally
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()
  private val simplifier = new ConstSimplifierForSmt()
  private var smtListener: SmtListener = new IdleSmtListener()
  private var _metrics: SolverContextMetrics = SolverContextMetrics.empty

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
  private val funDecls: mutable.Map[String, (FuncDecl[Sort], Int)] =
    new mutable.HashMap[String, (FuncDecl[Sort], Int)]()

  // The type of expressions of sorted elements.
  // The wildcard type helps scalac resolve specious type mismatches of the form
  // `Java-defined class Expr is invariant in type R`.
  type ExprSort = Expr[Sort]

  /**
   * The calls to z3context.mkConst consume 20% of the running time, according to VisualVM.
   * Let's cache the constants, if Z3 cannot do it well.
   * Again, the cache carries the context level, to support push and pop.
   */
  private val cellCache: mutable.Map[Int, (ExprSort, CellT, Int)] =
    new mutable.HashMap[Int, (ExprSort, CellT, Int)]

  /**
   * A cache for the in-relation between a set and its potential element.
   */
  private val inCache: mutable.Map[(Int, Int), (ExprSort, Int)] =
    new mutable.HashMap[(Int, Int), (ExprSort, Int)]

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
    cellCache.clear()
    inCache.clear()
    funDecls.clear()
    cellSorts.clear()
  }

  /**
   * Declare a constant for an arena cell.
   *
   * @param cell a (previously undeclared) cell
   */
  override def declareCell(cell: ArenaCell): Unit = {
    smtListener.onIntroCell(cell.id)

    if (maxCellIdPerContext.head >= cell.id) {
      // Checking consistency. When the user accidentally replaces a fresh arena with an older one,
      // we report it immediately. Otherwise, it is very hard to find the cause.
      val msg = "SMT %d: Declaring cell %d, while cell %d has been already declared. Damaged arena?"
        .format(id, cell.id, maxCellIdPerContext.head)
      flushAndThrow(new InternalCheckerError(msg, NullEx))
    } else {
      maxCellIdPerContext = cell.id +: maxCellIdPerContext.tail
    }

    log(s";; declare cell($cell): ${cell.cellType}")
    val cellSort = getOrMkCellSort(cell.cellType)
    log(s"(declare-const $cell $cellSort)")
    val cellName = cell.toString
    z3context.mkConstDecl(cellName, cellSort)
    val const = z3context.mkConst(cellName, cellSort)
    cellCache += (cell.id -> (const, cell.cellType, level))

    if (cell.id <= 1) {
      // Either FALSE or TRUE. Add an explicit assert at the SMT level.
      // Fix 333: avoid assertGroundExpr, as it simplifies our constants to false and true,
      // which renders this step useless.
      val z3expr =
        if (cell.id == 0) {
          z3context.mkEq(const, z3context.mkFalse().asInstanceOf[ExprSort])
        } else {
          z3context.mkEq(const, z3context.mkTrue().asInstanceOf[ExprSort])
        }

      log(s"(assert $z3expr)")
      z3solver.add(z3expr)
    }

    _metrics = _metrics.addNCells(1)
  }

  override def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = {
    val elemT = elem.cellType
    val setT = set.cellType
    val name = s"in_${elemT.signature}${elem.id}_${setT.signature}${set.id}"
    if (!inCache.contains((set.id, elem.id))) {
      smtListener.onIntroSmtConst(name)
      log(s";; declare edge predicate $name: Bool")
      log(s"(declare-const $name Bool)")
      nBoolConsts += 1
      val const = z3context.mkConst(name, z3context.getBoolSort)
      inCache += ((set.id, elem.id) -> ((const.asInstanceOf[ExprSort], level)))

      _metrics = _metrics.addNConsts(1)
    }
  }

  private def getInPred(setId: Int, elemId: Int): ExprSort = {
    inCache.get((setId, elemId)) match {
      case None =>
        val setT = cellCache(setId)._2
        val elemT = cellCache(elemId)._2
        val name = s"in_${elemT.signature}${elemId}_${setT.signature}$setId"
        logWriter.flush() // flush the SMT log
        throw new IllegalStateException(
            s"SMT $id: The Boolean constant $name (set membership) is missing from the SMT context")

      case Some((const, _)) =>
        const
    }
  }

  /**
   * Check whether the current view of the SMT solver is consistent with arena.
   *
   * @param arena an arena
   */
  override def checkConsistency(arena: Arena): Unit = {
    val topId = arena.topCell.id
    if (maxCellIdPerContext.head > topId) {
      // Checking consistency. When the user accidentally replaces a fresh arena with an older one,
      // we report it immediately. Otherwise, it is very hard to find the cause.
      val msg = "SMT %d: Declaring cell %d, while cell %d has been already declared. Damaged arena?"
        .format(id, topId, maxCellIdPerContext.head)
      flushAndThrow(new InternalCheckerError(msg, NullEx))
    }
  }

  /**
   * Assert that a Boolean TLA+ expression holds true.
   *
   * @param ex a simplified TLA+ expression over cells
   */
  def assertGroundExpr(ex: TlaEx): Unit = {
    log(s";; assert ${UTFPrinter.apply(ex)}")
    val (z3expr, size) = toExpr(ex)
    _metrics = _metrics.addNSmtExprs(size)
    smtListener.onSmtAssert(ex, size)
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
    val (smtEx, _) = toExpr(ex)
    val z3expr = z3solver.getModel.eval(smtEx, true)
    if (z3expr.isBool) {
      val isTrue = z3expr.getBoolValue.equals(Z3_lbool.Z3_L_TRUE)
      ValEx(if (isTrue) TlaBool(true) else TlaBool(false)) // in undefined case, just return false
    } else if (z3expr.isIntNum) {
      ValEx(TlaInt(z3expr.asInstanceOf[IntNum].getBigInteger))
    } else {
      if (z3expr.isConst && z3expr.getSort.getName.toString.startsWith("Cell_")) {
        NameEx(z3expr.toString)
      } else {
        flushAndThrow(new SmtEncodingException(s"SMT $id: Expected an integer or Boolean, found: $z3expr", ex))
      }
    }
  }

  private def initLog(): PrintWriter = {
    // TODO Fix SMT logging to be able support logging to latest directory
    val writer = OutputManager.printWriter(OutputManager.runDir, s"log$id.smt")
    if (!config.debug) {
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
    if (config.debug) {
      logWriter.println(message)
    }
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
      val msg = s"SMT $id: Declaring twice the function associated with cell $cellName"
      flushAndThrow(new SmtEncodingException(msg, NullEx))
    } else {
      val domSort = getOrMkCellSort(argType)
      val cdmSort = getOrMkCellSort(resultType)
      log(s";; declare cell fun $funName")
      log(s"(declare-fun $funName ($domSort) $cdmSort)")
      val funDecl = z3context.mkFuncDecl(funName, domSort, cdmSort)
      funDecls += (funName -> (funDecl, level))
      _metrics = _metrics.addNConsts(1)
    }
  }

  /**
   * Get the current context level, that is the difference between the number of pushes and pops made so far.
   *
   * @return the current level, always non-negative.
   */
  override def contextLevel: Int = level

  /**
   * Push SMT context
   */
  override def push(): Unit = {
    log("(push) ;; becomes %d".format(level + 1))
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
      log("(pop) ;; becomes %d".format(level - 1))
      logWriter.flush() // good time to flush
      z3solver.pop()
      maxCellIdPerContext = maxCellIdPerContext.tail
      level -= 1
      // clean the caches
      cellSorts.retain((_, value) => value._2 <= level)
      funDecls.retain((_, value) => value._2 <= level)
      cellCache.retain((_, value) => value._3 <= level)
      inCache.retain((_, value) => value._2 <= level)
    }
  }

  override def pop(n: Int): Unit = {
    if (n > 0) {
      log("(pop %d) ;; becomes %d".format(n, level - n))
      logWriter.flush() // good time to flush
      z3solver.pop(n)
      maxCellIdPerContext = maxCellIdPerContext.drop(n)
      level -= n
      // clean the caches
      cellSorts.retain((_, value) => value._2 <= level)
      funDecls.retain((_, value) => value._2 <= level)
      cellCache.retain((_, value) => value._3 <= level)
      inCache.retain((_, value) => value._2 <= level)
    }
  }

  override def sat(): Boolean = {
    log("(check-sat)")
    val status = z3solver.check()
    log(s";; sat = ${status == Status.SATISFIABLE}")
    logWriter.flush() // good time to flush
    if (status == Status.UNKNOWN) {
      // that seems to be the only reasonable behavior
      val msg = s"SMT $id: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic."
      flushAndThrow(new SmtEncodingException(msg, NullEx))
    }
    status == Status.SATISFIABLE
  }

  override def satOrTimeout(timeoutSec: Long): Option[Boolean] = {
    if (timeoutSec <= 0) {
      Some(sat())
    } else {
      def setTimeout(tm: Long): Unit = {
        val params = z3context.mkParams()
        params.add("timeout", BigInt(tm).toInt)
        z3solver.setParameters(params)
      }
      // temporarily, change the timeout
      setTimeout(timeoutSec * 1000)
      log("(check-sat)")
      val status = z3solver.check()
      // set it to the maximum: Z3 is using 2^32 - 1, which is hard to pass in Java, so we can only set it to 2^31-1
      setTimeout(Int.MaxValue)
      logWriter.flush() // good time to flush
      status match {
        case Status.SATISFIABLE   => Some(true)
        case Status.UNSATISFIABLE => Some(false)
        case Status.UNKNOWN       => None
      }
    }
  }

  /**
   * Print the collected constraints in the SMTLIB2 format using Z3 API.
   *
   * @return a long string of statements in SMTLIB2 format as provided by Z3
   */
  def toSmtlib2: String = {
    z3solver.toString
  }

  def setSmtListener(listener: SmtListener): Unit = {
    smtListener = listener
  }

  /**
   * Get the current metrics in the solver context. The metrics may change when the other methods are called.
   *
   * @return the current metrics
   */
  override def metrics(): SolverContextMetrics = _metrics

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

          case _ =>
            log(s"(declare-sort $sig 0)")
            z3context.mkUninterpretedSort(sig)
          // In preliminary experiments, the following trick sped up solving by 30%.
          // TODO: Figure out whether we can always do that.
//            z3context.mkUninterpretedSort(sig + "_" + level)
        }

      cellSorts += (sig -> (newSort, level))
      newSort
    }
  }

  private def toExpr(ex: TlaEx): (ExprSort, Long) = {
    simplifier.simplifyShallow(ex) match {
      case NameEx(name) =>
        val nm = cellCache(ArenaCell.idFromName(name))._1 // the cached cell
        (nm, 1)

      case ValEx(TlaBool(false)) =>
        val bool = z3context.mkFalse()
        (bool.asInstanceOf[ExprSort], 1)

      case ValEx(TlaBool(true)) =>
        val bool = z3context.mkTrue()
        (bool.asInstanceOf[ExprSort], 1)

      case ValEx(TlaInt(num)) =>
        if (num.isValidLong) {
          val int = z3context.mkInt(num.toLong)
          (int.asInstanceOf[ExprSort], 1)
        } else {
          // support big integers, issue #450
          val n = z3context.mkInt(num.toString())
          (n.asInstanceOf[ExprSort], 1)
        }

      case OperEx(oper: TlaArithOper, lex, rex) =>
        // convert to an arithmetic expression
        toArithExpr(ex)

      case OperEx(oper: TlaArithOper, subex) =>
        // convert to an arithmetic expression
        toArithExpr(ex)

      case OperEx(TlaOper.eq, lhs @ NameEx(lname), rhs @ NameEx(rname)) =>
        if (ArenaCell.isValidName(lname) && ArenaCell.isValidName(rname)) {
          // just comparing cells
          val eq = z3context.mkEq(cellCache(ArenaCell.idFromName(lname))._1, cellCache(ArenaCell.idFromName(rname))._1)
          (eq.asInstanceOf[ExprSort], 1)
        } else {
          // comparing integers and Boolean to cells, Booleans to Booleans, and Integers to Integers
          val (le, ln) = toExpr(lhs)
          val (re, rn) = toExpr(rhs)
          val eq = toEqExpr(le.asInstanceOf[Expr[Sort]], re.asInstanceOf[Expr[Sort]])
          (eq.asInstanceOf[ExprSort], 1 + ln + rn)
        }

      case OperEx(TlaOper.eq, lhs, rhs) =>
        val (le, ln) = toExpr(lhs)
        val (re, rn) = toExpr(rhs)
        val eq = toEqExpr(le, re)
        (eq.asInstanceOf[ExprSort], 1 + ln + rn)

      case OperEx(TlaOper.ne, lhs, rhs) =>
        val (eq, n) = toExpr(OperEx(TlaOper.eq, lhs, rhs))
        (z3context.mkNot(eq.asInstanceOf[BoolExpr]).asInstanceOf[ExprSort], 1 + n)

      case OperEx(ApalacheOper.distinct, args @ _*) =>
        val (es, ns) = (args map toExpr).unzip
        val distinct = z3context.mkDistinct(es: _*)
        (distinct.asInstanceOf[ExprSort],
            ns.foldLeft(1L) {
          _ + _
        })

      case OperEx(TlaBoolOper.and, args @ _*) =>
        val (es, ns) = (args map toExpr).unzip
        val and = z3context.mkAnd(es.map(_.asInstanceOf[BoolExpr]): _*)
        (and.asInstanceOf[ExprSort],
            ns.foldLeft(1L) {
          _ + _
        })

      case OperEx(TlaBoolOper.or, args @ _*) =>
        val (es, ns) = (args map toExpr).unzip
        val or = z3context.mkOr(es.map(_.asInstanceOf[BoolExpr]): _*)
        (or.asInstanceOf[ExprSort],
            ns.foldLeft(1L) {
          _ + _
        })

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        val (lhsZ3, ln) = toExpr(lhs)
        val (rhsZ3, rn) = toExpr(rhs)
        val imp = z3context.mkImplies(lhsZ3.asInstanceOf[BoolExpr], rhsZ3.asInstanceOf[BoolExpr])
        (imp.asInstanceOf[ExprSort], 1 + ln + rn)

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        val (lhsZ3, ln) = toExpr(lhs)
        val (rhsZ3, rn) = toExpr(rhs)
        val equiv = z3context.mkEq(lhsZ3.asInstanceOf[BoolExpr], rhsZ3.asInstanceOf[BoolExpr])
        (equiv.asInstanceOf[ExprSort], 1 + ln + rn)

      case OperEx(TlaControlOper.ifThenElse, cond, thenExpr, elseExpr) =>
        val (boolCond, cn) = toExpr(cond)
        val (thenZ3, tn) = toExpr(thenExpr)
        val (elseZ3, en) = toExpr(elseExpr)
        val ite = z3context.mkITE(boolCond.asInstanceOf[BoolExpr], thenZ3, elseZ3)
        (ite, 1 + cn + tn + en)

      case OperEx(TlaBoolOper.not, e) =>
        val (exZ3, n) = toExpr(e)
        val not = z3context.mkNot(exZ3.asInstanceOf[BoolExpr])
        (not.asInstanceOf[ExprSort], 1 + n)

      case OperEx(TlaSetOper.notin, elem, set) =>
        val (e, n) = toExpr(OperEx(TlaSetOper.in, elem, set))
        val not = z3context.mkNot(e.asInstanceOf[BoolExpr])
        (not.asInstanceOf[ExprSort], 1 + n)

      case OperEx(TlaSetOper.in, NameEx(elemName), NameEx(setName)) =>
        val setId = ArenaCell.idFromName(setName)
        val elemId = ArenaCell.idFromName(elemName)
        (getInPred(setId, elemId), 1)

      // the old implementation allowed us to do that, but the new one is encoding edges directly
      case OperEx(TlaSetOper.in, ValEx(TlaInt(_)), NameEx(_)) | OperEx(TlaSetOper.in, ValEx(TlaBool(_)), NameEx(_)) =>
        flushAndThrow(new InvalidTlaExException(s"SMT $id: Preprocessing introduced a literal inside tla.in: $ex", ex))

      case _ =>
        flushAndThrow(new InvalidTlaExException(s"SMT $id: Unexpected TLA+ expression: $ex", ex))
    }
  }

  private def toEqExpr[R <: Sort](le: Expr[R], re: Expr[R]) = {
    (le, re) match {
      case (_: BoolExpr, _: BoolExpr) | (_: IntExpr, _: IntExpr) =>
        z3context.mkEq(le, re)

      case (_: IntExpr, _: Expr[R]) =>
        // comparing an integer constant and a cell of integer type, which is declared as integer
        z3context.mkEq(le, re)

      case (_: Expr[R], _: IntExpr) =>
        // comparing an integer constant and a cell of integer type, which is declared as integer
        z3context.mkEq(le, re)

      case (_: Expr[R], _: Expr[R]) =>
        // comparing a cell constant against a function application
        z3context.mkEq(le, re)

      case _ =>
        flushAndThrow(throw new CheckerException(s"SMT $id: Incomparable expressions", NullEx))
    }
  }

  // Workaround for impedence bitween with Java Generics and Scala parametric types
  // See, e.g., https://stackoverflow.com/a/16430462/1187277
  private def mkArithCmp(ctor: (Expr[ArithSort], Expr[ArithSort]) => BoolExpr)(a: ExprSort, b: ExprSort): ExprSort = {
    ctor(a.asInstanceOf[Expr[ArithSort]], b.asInstanceOf[Expr[ArithSort]]).asInstanceOf[ExprSort]
  }

  private def mkArithOp(ctor: (Expr[ArithSort], Expr[ArithSort]) => ArithExpr[ArithSort])(a: ExprSort,
      b: ExprSort): ExprSort = {
    ctor(a.asInstanceOf[Expr[ArithSort]], b.asInstanceOf[Expr[ArithSort]]).asInstanceOf[ExprSort]
  }

  private def toArithExpr(ex: TlaEx): (ExprSort, Long) = {

    def mkBinEx(ctor: (ExprSort, ExprSort) => ExprSort, left: TlaEx, right: TlaEx): (ExprSort, Long) = {
      val (le, ln) = toArithExpr(left)
      val (re, rn) = toArithExpr(right)
      val z3ex = ctor(le, re)
      (z3ex, 1 + ln + rn)
    }

    ex match {
      case ValEx(TlaInt(num)) =>
        if (num.isValidLong) {
          val n = z3context.mkInt(num.toLong)
          (n.asInstanceOf[ExprSort], 1)
        } else {
          // support big integers, issue #450
          val n = z3context.mkInt(num.toString())
          (n.asInstanceOf[ExprSort], 1)
        }

      case NameEx(name) =>
        val n = z3context.mkIntConst(name) // TODO: incompatible sorts?
        (n.asInstanceOf[ExprSort], 1)

      case OperEx(TlaArithOper.lt, left, right) =>
        mkBinEx(mkArithCmp(z3context.mkLt), left, right)

      case OperEx(TlaArithOper.le, left, right) =>
        mkBinEx(mkArithCmp(z3context.mkLe), left, right)

      case OperEx(TlaArithOper.gt, left, right) =>
        mkBinEx(mkArithCmp(z3context.mkGt), left, right)

      case OperEx(TlaArithOper.ge, left, right) =>
        mkBinEx(mkArithCmp(z3context.mkGe), left, right)

      case OperEx(TlaArithOper.plus, left, right) =>
        mkBinEx(mkArithOp((l, r) => z3context.mkAdd(l, r)), left, right)

      case OperEx(TlaArithOper.minus, left, right) =>
        mkBinEx(mkArithOp((l, r) => z3context.mkSub(l, r)), left, right)

      case OperEx(TlaArithOper.mult, left, right) =>
        mkBinEx(mkArithOp((l, r) => z3context.mkMul(l, r)), left, right)

      case OperEx(TlaArithOper.div, left, right) =>
        mkBinEx(mkArithOp(z3context.mkDiv), left, right)

      case OperEx(TlaArithOper.mod, left, right) =>
        val (le, ln) = toArithExpr(left)
        val (re, rn) = toArithExpr(right)
        val mod = z3context.mkMod(le.asInstanceOf[IntExpr], re.asInstanceOf[IntExpr])
        (mod.asInstanceOf[ExprSort], 1 + ln + rn)

      case OperEx(TlaArithOper.uminus, subex) =>
        val (e, n) = toArithExpr(subex)
        val minus = z3context.mkUnaryMinus(e.asInstanceOf[IntExpr])
        (minus.asInstanceOf[ExprSort], 1 + n)

      case OperEx(TlaControlOper.ifThenElse, cond, thenExpr, elseExpr) =>
        val (boolCond, cn) = toExpr(cond)
        val (thenZ3, tn) = toArithExpr(thenExpr)
        val (elseZ3, en) = toArithExpr(elseExpr)
        val ite = z3context.mkITE(boolCond.asInstanceOf[BoolExpr], thenZ3, elseZ3)
        (ite, 1 + cn + tn + en)

      case _ =>
        flushAndThrow(new InvalidTlaExException(s"SMT $id: Unexpected arithmetic expression: $ex", ex))
    }
  }

  /**
   * Flush the SMT log and throw the provided exception.
   *
   * @param e an exception to throw
   * @return nothing, as an exception is unconditionally thrown
   */
  private def flushAndThrow(e: Exception): Nothing = {
    logWriter.flush() // flush the SMT log
    throw e
  }
}

object Z3SolverContext {
  private var nextId: AtomicLong = new AtomicLong(0)

  private def createId(): Long = {
    nextId.getAndIncrement()
  }

  /**
   * The names of all parameters that are used to set the random seeds in z3.
   */
  val RANDOM_SEED_PARAMS: List[String] =
    List("sat.random_seed", "smt.random_seed", "fp.spacer.random_seed", "sls.random_seed")
}

package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.profiler.{IdleSmtListener, SmtListener}
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.UTFPrinter
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_lbool
import com.typesafe.scalalogging.LazyLogging

import java.io.PrintWriter
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.locks.ReentrantLock
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
 * <p> An implementation of a SolverContext using Z3. Note that this class overrides the global z3 settings
 * `sat.random_seed`, `smt.random_seed`, `fp.spacer.random_seed`, and `sls.random_seed` with `config.randomSeed`.
 * Although it is usually not a good idea to override the global settings, we do it to isolate the code specific to z3
 * in this class. </p>
 *
 * @author
 *   Igor Konnov, Rodrigo Otoni
 */
class Z3SolverContext(val config: SolverConfig) extends SolverContext with LazyLogging {
  private val id: Long = Z3SolverContext.createId()

  logger.debug(s"Creating Z3 solver context ${id}")

  /**
   * A log writer, for debugging purposes.
   */
  private val logWriters: Iterable[PrintWriter] = initLogs()

  // Set the global configuration parameters for Z3 modules.
  Z3SolverContext.RANDOM_SEED_PARAMS.foreach { p =>
    Global.setParameter(p, config.randomSeed.toString)
    log(";; %s = %s".format(p, Global.getParameter(p)))
  }

  private def encoding: SMTEncoding = config.smtEncoding

  var level: Int = 0
  var nBoolConsts: Int = 0 // the solver introduces Boolean constants internally
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()
  private val simplifier = new ConstSimplifierForSmt()
  private var smtListener: SmtListener = new IdleSmtListener()
  private var _metrics: SolverContextMetrics = SolverContextMetrics.empty

  // Set up parameters to Z3; the list of parameters can be seen by passing the -p flag to Z3
  val params = z3context.mkParams()
  // Set random seed. We are also setting it via global parameters above, but `Global.setParameter()` says:
  // "When a Z3 module is initialized it will use the value of these parameters when Z3_params objects are not provided."
  // Note: when the user sets z3.smt.logic = QF_LIA, z3 complains about random_seed.
  // https://github.com/apalache-mc/apalache/issues/2989
  params.add("random_seed", config.randomSeed)
  config.z3Params.foreach { case (k, v) =>
    if (v.isInstanceOf[Int]) {
      params.add(k, v.asInstanceOf[Int])
    } else if (v.isInstanceOf[Boolean]) {
      params.add(k, v.asInstanceOf[Boolean])
    } else if (v.isInstanceOf[Double]) {
      params.add(k, v.asInstanceOf[Double])
    } else {
      params.add(k, v.toString)
    }
  }
  z3solver.setParameters(params)
  log(s";; ${params}")

  /**
   * Caching one uninterpreted sort for each cell signature. For integers, the integer sort.
   */
  private val cellSorts: mutable.Map[String, (Sort, Int)] =
    new mutable.HashMap[String, (Sort, Int)]

  /**
   * Uninterpreted functions C -> C associated with function cells. Since context operations may clear function
   * declaration, we carry the context level in the map and clean the function declarations on pop.
   */
  private val funDecls: mutable.Map[String, (FuncDecl[Sort], Int)] =
    new mutable.HashMap[String, (FuncDecl[Sort], Int)]()

  // The type of expressions of sorted elements.
  // The wildcard type helps scalac resolve specious type mismatches of the form
  // `Java-defined class Expr is invariant in type R`.
  type ExprSort = Expr[Sort]

  /**
   * The calls to z3context.mkConst consume 20% of the running time, according to VisualVM. Let's cache the constants,
   * if Z3 cannot do it well. Again, the cache carries the context level, to support push and pop. To support SSA arrays
   * representing sets, the cache stores a list of constants. The list is required to support incremental solving, since
   * different context levels can have different SSA arrays.
   */
  private val cellCache: mutable.Map[Int, ListBuffer[(ExprSort, CellT, Int)]] =
    new mutable.HashMap[Int, ListBuffer[(ExprSort, CellT, Int)]]

  /**
   * A cache for the in-relation between a set and its potential element.
   */
  private val inCache: mutable.Map[(Int, Int), (ExprSort, Int)] =
    new mutable.HashMap[(Int, Int), (ExprSort, Int)]

  /**
   * A cache for declarations of constant arrays of different types. Used in the arrays encoding to avoid duplicate
   * declarations.
   */
  private val constantArrayCache: mutable.Map[Sort, (Expr[Sort], Int)] =
    new mutable.HashMap[Sort, (ExprSort, Int)]

  /**
   * Caching the default value for each cell signature. For integers, the value 0.
   */
  private val cellDefaults: mutable.Map[String, (ExprSort, Int)] =
    new mutable.HashMap[String, (ExprSort, Int)]

  /**
   * Sometimes, we lose a fresh arena in the rewriting rules. As this situation is very hard to debug, we are tracking
   * here the largest cell id per SMT context. If the user is trying to add a cell with a smaller id, there is a good
   * chance that a fresher arena was overwritten with an older one. To find bugs as soon as possible, we crash
   * immediately.
   */
  private var maxCellIdPerContext = List(-1)

  private trait ContextState
  private case class Running() extends ContextState
  private case class Disposed() extends ContextState

  // the state of the context: Running or Disposed
  private var state: ContextState = Running()

  // the lock shared between the context and the statistics thread
  private val statisticsLock: ReentrantLock = new ReentrantLock()
  // start a new thread to collect statistics
  private val statisticsThread = new Thread(() => {
    var interrupted = false
    while (state == Running() && !interrupted) {
      // Sleep for a while.
      // If we call printStatistics right away, we can easily run into a race condition with Z3 initializing.
      // This produces a core dump.
      // make sure that the context is not being disposed right now. Otherwise, we can get a nice core dump.
      statisticsLock.lock()
      try {
        Thread.sleep(config.z3StatsSec * 1000)
        printStatistics()
      } catch {
        case _: InterruptedException =>
          // terminate the thread immediately upon interruption
          logger.info(s"Finishing the statistics thread ${id}")
          interrupted = true
      } finally {
        statisticsLock.unlock()
      }
    }
  })

  if (config.debug && config.z3StatsSec > 0) {
    statisticsThread.start()
  }

  /**
   * Dispose whatever has to be disposed in the end.
   */
  override def dispose(): Unit = {
    logger.debug(s"Disposing Z3 solver context ${id}")
    state = Disposed()
    // Try to obtain the lock, to let the statistics thread finish its work.
    // If it is stuck for some reason, continue after the timeout in any case.
    statisticsThread.interrupt()
    statisticsLock.tryLock(2 * config.z3StatsSec, java.util.concurrent.TimeUnit.SECONDS)
    try {
      if (config.debug) {
        printStatistics()
      }
      z3context.close()
      closeLogs()
      cellCache.clear()
      inCache.clear()
      funDecls.clear()
      cellSorts.clear()
    } finally {
      // it's not that important at this point, but let's unlock it for the piece of mind
      statisticsLock.unlock()
    }
  }

  /**
   * Declare a constant for an arena cell.
   *
   * @param cell
   *   a (previously undeclared) cell
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
    val const = z3context.mkConst(cellName, cellSort)
    cellCache += (cell.id -> ListBuffer((const, cell.cellType, level)))

    // If arrays are used, they are initialized here.
    if (cellSort.isInstanceOf[ArraySort[_, _]] && !cell.isUnconstrained) {
      val arrayInitializer =
        if (cell.cellType.isInstanceOf[InfSetT]) {
          // Infinite sets are not cached because they are not empty
          z3context.mkEq(const, getOrMkCellDefaultValue(cellSort, isInfiniteSet = true))
        } else {
          constantArrayCache.get(cellSort) match {
            case Some(emptySet) =>
              z3context.mkEq(const, emptySet._1)
            case None =>
              constantArrayCache += (cellSort -> (const, level))
              z3context.mkEq(const, getOrMkCellDefaultValue(cellSort))
          }
        }

      log(s"(assert $arrayInitializer)")
      z3solver.add(arrayInitializer)
      _metrics = _metrics.addNSmtExprs(1)
    }

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
      _metrics = _metrics.addNSmtExprs(1)
    }

    _metrics = _metrics.addNCells(1)
  }

  override def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = {
    val elemT = elem.cellType
    val setT = set.cellType
    val name = s"in_${elemT.signature}${elem.id}_${setT.signature}${set.id}"
    if (!inCache.contains((set.id, elem.id))) {
      // The concept of an in-relation is not present in the arrays encoding
      if (encoding == SMTEncoding.OOPSLA19 || encoding == SMTEncoding.FunArrays) {
        smtListener.onIntroSmtConst(name)
        log(s";; declare edge predicate $name: Bool")
        log(s"(declare-const $name Bool)")
        nBoolConsts += 1
        val const = z3context.mkConst(name, z3context.getBoolSort)
        inCache += ((set.id, elem.id) -> ((const.asInstanceOf[ExprSort], level)))
        _metrics = _metrics.addNConsts(1)
      }
    }
  }

  private def getInPred(setId: Int, elemId: Int): ExprSort = {
    inCache.get((setId, elemId)) match {
      case None =>
        val setT = cellCache(setId).head._2
        val elemT = cellCache(elemId).head._2
        val name = s"in_${elemT.signature}${elemId}_${setT.signature}$setId"
        flushLogs()
        throw new IllegalStateException(
            s"SMT $id: The Boolean constant $name (set membership) is missing from the SMT context")

      case Some((const, _)) =>
        const
    }
  }

  private def mkSelect(arrayId: Int, elemId: Int): ExprSort = {
    val array = cellCache(arrayId).head._1
    val elem = cellCache(elemId).head._1

    z3context.mkSelect(array.asInstanceOf[ArrayExpr[Sort, Sort]], elem.asInstanceOf[Expr[Sort]]).asInstanceOf[ExprSort]
  }

  private def mkNestedSelect(outerArrayId: Int, innerArrayId: Int, elemId: Int): ExprSort = {
    val outerArray = cellCache(outerArrayId).head._1
    val innerArray = cellCache(innerArrayId).head._1
    val elem = cellCache(elemId).head._1

    val innerSelect = z3context
      .mkSelect(innerArray.asInstanceOf[ArrayExpr[Sort, Sort]], elem.asInstanceOf[Expr[Sort]])
      .asInstanceOf[ExprSort]
    z3context
      .mkSelect(outerArray.asInstanceOf[ArrayExpr[Sort, Sort]], innerSelect.asInstanceOf[Expr[Sort]])
      .asInstanceOf[ExprSort]
  }

  private def mkStore(arrayId: Int, IndexId: Int, elemId: Int = 1): ExprSort = {
    val (array, arrayT, _) = cellCache(arrayId).head
    val (index, indexT, _) = cellCache(IndexId).head
    val (elem, elemT, _) = cellCache(elemId).head // Id 1 caches the value true

    val oldEntry = s"${arrayT.signature}$arrayId[${indexT.signature}$IndexId]"
    val newEntry = s"${elemT.signature}$elemId"
    log(s";; declare update of $oldEntry to $newEntry")

    val updatedArray = updateArrayConst(arrayId)
    val store = z3context.mkStore(array.asInstanceOf[Expr[ArraySort[Sort, Sort]]], index.asInstanceOf[Expr[Sort]],
        elem.asInstanceOf[Expr[Sort]])

    val eqStore = z3context.mkEq(updatedArray, store)
    eqStore.asInstanceOf[ExprSort]
  }

  private def mkUnchangedArray(arrayId: Int): ExprSort = {
    if (cellCache(arrayId).size > 1) {
      val currentArray = cellCache(arrayId).head._1
      val oldArray = cellCache(arrayId).tail.head._1
      val eqUnchanged = z3context.mkEq(currentArray, oldArray)
      eqUnchanged.asInstanceOf[ExprSort]
    } else if (cellCache(arrayId).size == 1) {
      // If arrayId refers to an array with a single SSA representation there is nothing to be done
      z3context.mkTrue().asInstanceOf[ExprSort]
    } else {
      flushLogs()
      throw new IllegalStateException(
          s"SMT $id: Corrupted cellCache, $arrayId key is present, but it does not refer to any array.")
    }
  }

  private def updateArrayConst(arrayId: Int): ExprSort = {
    val (array, arrayT, _) = cellCache(arrayId).head
    val newSSAIndex = cellCache(arrayId).size
    val updatedArrayName = array.toString.split("_").head + "_" + newSSAIndex
    val arraySort = getOrMkCellSort(arrayT)
    log(s"(declare-const $updatedArrayName $arraySort)")
    val updatedArray = z3context.mkConst(updatedArrayName, arraySort)
    cellCache += (arrayId -> cellCache(arrayId).prepend((updatedArray, arrayT, level)))
    _metrics = _metrics.addNConsts(1)
    updatedArray.asInstanceOf[ExprSort]
  }

  /**
   * Check whether the current view of the SMT solver is consistent with arena.
   *
   * @param arena
   *   an arena
   */
  override def checkConsistency(arena: PureArenaAdapter): Unit = {
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
   * @param ex
   *   a simplified TLA+ expression over cells
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
   * Evaluate a ground TLA+ expression in the current model, which is available after a call to sat(). This method
   * assumes that the outcome is one of the basic types: a Boolean, integer, or a cell constant. If not, it throws
   * SmtEncodingException.
   *
   * @param ex
   *   an expression to evaluate
   * @return
   *   a TLA+ value
   */
  def evalGroundExpr(ex: TlaEx): TlaEx = {
    val (smtEx, _) = toExpr(ex)
    val z3expr = z3solver.getModel.eval(smtEx, true)
    if (z3expr.isBool) {
      z3expr.getBoolValue match {
        case Z3_lbool.Z3_L_TRUE =>
          tla.bool(true)
        case Z3_lbool.Z3_L_FALSE =>
          tla.bool(false)
        case _ =>
          // If we cannot get a result from evaluating the model, we query the solver
          z3solver.add(z3expr.asInstanceOf[BoolExpr])
          tla.bool(sat())
      }
    } else if (z3expr.isIntNum) {
      tla.int(z3expr.asInstanceOf[IntNum].getBigInteger)
    } else {
      if (z3expr.isConst && z3expr.getSort.getName.toString.startsWith("Cell_")) {
        tla.name(z3expr.toString, TlaType1.fromTypeTag(ex.typeTag))
      } else {
        flushAndThrow(new SmtEncodingException(s"SMT $id: Expected an integer or Boolean, found: $z3expr", ex))
      }
    }
  }

  /**
   * Initialize up to two log writers, one in the run directory and one in the custom run directory, if those are set.
   */
  private def initLogs(): Iterable[PrintWriter] = {
    val filePart = s"log$id.smt"
    val writers =
      (OutputManager.runDirPathOpt ++ OutputManager.customRunDirPathOpt).map(OutputManager.printWriter(_, filePart))

    if (!config.debug) {
      writers.foreach { writer =>
        writer.println("Logging is disabled (Z3SolverContext.debug = false). Activate with --debug.")
        writer.flush()
      }
    }

    writers
  }

  /**
   * Log message to the logging file(s). This is helpful to debug the SMT encoding.
   *
   * @param message
   *   message text, called by name, so evaluated only when needed
   */
  def log(message: => String): Unit = {
    if (config.debug) {
      logWriters.foreach(_.println(message))
    }
  }

  /** Flush all log writers. */
  private def flushLogs(): Unit = logWriters.foreach(_.flush())

  /** Close all log writers. */
  private def closeLogs(): Unit = logWriters.foreach(_.close())

  /**
   * Introduce an uninterpreted function associated with a cell.
   *
   * @param argType
   *   an argument type
   * @param resultType
   *   a result type
   * @return
   *   the name of the new function (declared in SMT)
   */
  def declareCellFun(cellName: String, argType: CellT, resultType: CellT): Unit = {
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
   * @return
   *   the current level, always non-negative.
   */
  override def contextLevel: Int = level

  /**
   * Push SMT context
   */
  override def push(): Unit = {
    log("(push) ;; becomes %d".format(level + 1))
    flushLogs() // good time to flush
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
      flushLogs() // good time to flush
      z3solver.pop()
      maxCellIdPerContext = maxCellIdPerContext.tail
      level -= 1
      // clean the caches
      cellSorts.filterInPlace((_, value) => value._2 <= level)
      funDecls.filterInPlace((_, value) => value._2 <= level)
      cellCache.foreachEntry((_, valueList) => valueList.filterInPlace(value => value._3 <= level))
      cellCache.filterInPlace((_, valueList) => valueList.nonEmpty)
      inCache.filterInPlace((_, value) => value._2 <= level)
      constantArrayCache.filterInPlace((_, value) => value._2 <= level)
      cellDefaults.filterInPlace((_, value) => value._2 <= level)
    }
  }

  override def pop(n: Int): Unit = {
    if (n > 0) {
      log("(pop %d) ;; becomes %d".format(n, level - n))
      flushLogs() // good time to flush
      z3solver.pop(n)
      maxCellIdPerContext = maxCellIdPerContext.drop(n)
      level -= n
      // clean the caches
      cellSorts.filterInPlace((_, value) => value._2 <= level)
      funDecls.filterInPlace((_, value) => value._2 <= level)
      cellCache.foreachEntry((_, valueList) => valueList.filterInPlace(value => value._3 <= level))
      cellCache.filterInPlace((_, valueList) => valueList.nonEmpty)
      inCache.filterInPlace((_, value) => value._2 <= level)
      constantArrayCache.filterInPlace((_, value) => value._2 <= level)
      cellDefaults.filterInPlace((_, value) => value._2 <= level)
    }
  }

  override def sat(): Boolean = {
    log("(check-sat)")
    flushLogs() // good time to flush
    val status = z3solver.check()
    log(s";; sat = ${status.name()}")
    flushLogs() // good time to flush
    if (status == Status.UNKNOWN) {
      // that seems to be the only reasonable behavior
      val msg = s"SMT $id: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic."
      flushAndThrow(new SmtEncodingException(msg, NullEx))
    }
    status == Status.SATISFIABLE
  }

  override def satOrTimeout(timeoutSec: Int): Option[Boolean] = {
    if (timeoutSec <= 0) {
      Some(sat())
    } else {
      def setTimeout(tm: Int): Unit = {
        params.add("timeout", tm)
        z3solver.setParameters(params)
        log(s";; ${params}")
      }
      // Z3 expects `timeout` to be in milliseconds passed as unsigned int, i.e., with a maximum value of 2^32 - 1.
      // The Z3 Java API only allows passing it as signed int, i.e., the maximum allowed millisecond value is 2^31 - 1 (`Int.MaxValue`).
      // Check that `timeoutSec` converted to milliseconds fits without truncation.
      require(timeoutSec < Int.MaxValue / 1000, s"Expected a timeout of <=${Int.MaxValue / 1000} seconds.")
      // temporarily, change the timeout
      setTimeout(timeoutSec * 1000)
      log("(check-sat)")
      flushLogs() // good time to flush
      val status = z3solver.check()
      log(s";; sat = ${status.name()}")
      flushLogs() // good time to flush
      // return timeout to maximum
      setTimeout(Int.MaxValue)
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
   * @return
   *   a long string of statements in SMTLIB2 format as provided by Z3
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
   * @return
   *   the current metrics
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
          case CellTFrom(BoolT1) =>
            z3context.getBoolSort

          case CellTFrom(IntT1) =>
            z3context.getIntSort

          case CellTFrom(SetT1(elemType)) if encoding == SMTEncoding.Arrays =>
            z3context.mkArraySort(getOrMkCellSort(CellTFrom(elemType)), z3context.getBoolSort)

          case InfSetT(elemType) if encoding == SMTEncoding.Arrays =>
            z3context.mkArraySort(getOrMkCellSort(elemType), z3context.getBoolSort)

          case PowSetT(domType) if encoding == SMTEncoding.Arrays =>
            z3context.mkArraySort(getOrMkCellSort(CellTFrom(domType)), z3context.getBoolSort)

          case FinFunSetT(domType, cdmType) if encoding == SMTEncoding.Arrays =>
            val funSort = z3context.mkArraySort(mkCellElemSort(domType), mkCellElemSort(cdmType))
            z3context.mkArraySort(funSort, z3context.getBoolSort)

          case CellTFrom(FunT1(argType, resType))
              if encoding == SMTEncoding.Arrays || encoding == SMTEncoding.FunArrays =>
            z3context.mkArraySort(getOrMkCellSort(CellTFrom(argType)), getOrMkCellSort(CellTFrom(resType)))

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

  private def getOrMkCellDefaultValue(cellSort: Sort, isInfiniteSet: Boolean = false): ExprSort = {
    val sig = "Cell_" + cellSort
    val sort = cellDefaults.get(sig)
    if (sort.isDefined) {
      sort.get._1
    } else {
      // Explicitly annotate existential type of `newDefault`. Fixes "inferred existential type ..., which cannot be
      // expressed by wildcards, should be enabled by making the implicit value scala.language.existentials visible."
      val newDefault: Expr[_1] forSome { type _1 <: Sort } = cellSort match {
        case _: BoolSort =>
          z3context.mkFalse()

        case _: IntSort =>
          z3context.mkInt(0)

        case arraySort: ArraySort[_, _] if isInfiniteSet =>
          // Infinite sets are not cached because they are not empty
          return z3context.mkConstArray(arraySort.getDomain, z3context.mkTrue()).asInstanceOf[ExprSort]

        case arraySort: ArraySort[_, _] if !isInfiniteSet =>
          z3context.mkConstArray(arraySort.getDomain, getOrMkCellDefaultValue(arraySort.getRange))

        case _ =>
          log(s"(declare-const $sig $cellSort)")
          z3context.mkConst(sig, cellSort)
      }

      cellDefaults += (sig -> (newDefault.asInstanceOf[ExprSort], level))
      newDefault.asInstanceOf[ExprSort]
    }
  }

  private def mkCellElemSort(cellType: CellT): Sort = {
    cellType match {
      case CellTFrom(BoolT1) =>
        z3context.getBoolSort

      case CellTFrom(IntT1) =>
        z3context.getIntSort

      case CellTFrom(SetT1(elemType)) if encoding == SMTEncoding.Arrays =>
        mkCellElemSort(CellTFrom(elemType))

      case PowSetT(domType) if encoding == SMTEncoding.Arrays =>
        mkCellElemSort(CellTFrom(domType))

      case FinFunSetT(argType, cdmType) if encoding == SMTEncoding.Arrays =>
        mkCellElemSort(CellTFrom(FunT1(argType.toTlaType1, cdmType.toTlaType1)))

      case CellTFrom(FunT1(argType, resType)) if encoding == SMTEncoding.Arrays || encoding == SMTEncoding.FunArrays =>
        z3context.mkArraySort(mkCellElemSort(CellTFrom(argType)), mkCellElemSort(CellTFrom(resType)))

      case _ =>
        z3context.mkUninterpretedSort("Cell_" + cellType.signature)
    }
  }

  private def toExpr(ex: TlaEx): (ExprSort, Long) = {
    simplifier.simplifyShallow(ex) match {
      case NameEx(name) =>
        val nm = cellCache(ArenaCell.idFromName(name)).head._1 // the cached cell
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

      case arithEx @ OperEx(_: TlaArithOper, _, _) =>
        // convert to an arithmetic expression
        toArithExpr(arithEx)

      case arithEx @ OperEx(_: TlaArithOper, _) =>
        // convert to an arithmetic expression
        toArithExpr(arithEx)

      case OperEx(TlaOper.eq, lhs @ NameEx(lname), rhs @ NameEx(rname)) =>
        if (ArenaCell.isValidName(lname) && ArenaCell.isValidName(rname)) {
          // just comparing cells
          val eq = z3context
            .mkEq(cellCache(ArenaCell.idFromName(lname)).head._1, cellCache(ArenaCell.idFromName(rname)).head._1)
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
        val (eq, n) = toExpr(tla.eql(tla.unchecked(lhs), tla.unchecked(rhs)))
        (z3context.mkNot(eq.asInstanceOf[BoolExpr]).asInstanceOf[ExprSort], 1 + n)

      case OperEx(ApalacheInternalOper.distinct, args @ _*) =>
        if (args.length < 2) {
          // Produce true for a singleton set or an empty set. Otherwise, we cannot replay the SMT log in CVC5.
          (z3context.mkTrue().asInstanceOf[ExprSort], 1)
        } else {
          val (es, ns) = (args.map(toExpr)).unzip
          val distinct = z3context.mkDistinct(es: _*)
          (distinct.asInstanceOf[ExprSort], ns.sum + 1)
        }

      case OperEx(TlaBoolOper.and, args @ _*) =>
        val (es, ns) = (args.map(toExpr)).unzip
        val and = z3context.mkAnd(es.map(_.asInstanceOf[BoolExpr]): _*)
        (and.asInstanceOf[ExprSort], ns.sum + 1)

      case OperEx(TlaBoolOper.or, args @ _*) =>
        val (es, ns) = (args.map(toExpr)).unzip
        val or = z3context.mkOr(es.map(_.asInstanceOf[BoolExpr]): _*)
        (or.asInstanceOf[ExprSort], ns.sum + 1)

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
        val (e, n) = toExpr(tla.in(tla.unchecked(elem), tla.unchecked(set)))
        val not = z3context.mkNot(e.asInstanceOf[BoolExpr])
        (not.asInstanceOf[ExprSort], 1 + n)

      case OperEx(TlaSetOper.in, NameEx(elemName), NameEx(setName)) =>
        val setId = ArenaCell.idFromName(setName)
        val elemId = ArenaCell.idFromName(elemName)
        (getInPred(setId, elemId), 1)

      case OperEx(ApalacheInternalOper.selectInSet, elemNameEx @ NameEx(elemName), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.Arrays =>
            val setId = ArenaCell.idFromName(setName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkSelect(setId, elemId), 1)
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.in(tla.unchecked(elemNameEx),
                    tla.unchecked(setNameEx))) // Set membership in the oopsla19 encoding
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.selectInFun, elemNameEx @ NameEx(elemName), funNameEx @ NameEx(funName)) =>
        encoding match {
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            val funId = ArenaCell.idFromName(funName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkSelect(funId, elemId), 1)
          case SMTEncoding.OOPSLA19 =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(funNameEx)))
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.selectInSet,
              OperEx(ApalacheInternalOper.selectInFun, NameEx(elemName), NameEx(funName)), NameEx(setName)) =>
        encoding match {
          case SMTEncoding.Arrays =>
            // Nested selects are used to check if the result of a function application is in a given set
            val set2Id = ArenaCell.idFromName(setName)
            val set1Id = ArenaCell.idFromName(funName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkNestedSelect(set2Id, set1Id, elemId), 1)
          case oddEncodingType =>
            // Nested selects should not happen in the oopsla19 encoding
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.storeInSet, elemNameEx @ NameEx(elemName), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.Arrays =>
            val setId = ArenaCell.idFromName(setName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkStore(setId, elemId), 1) // elem is the arg of the SMT store here, since the range is fixed for sets
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.in(tla.unchecked(elemNameEx),
                    tla.unchecked(setNameEx))) // Set membership in the oopsla19 encoding
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.storeInSet, NameEx(elemName), NameEx(funName), NameEx(argName)) =>
        encoding match {
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            // Updates a function for a given argument
            val funId = ArenaCell.idFromName(funName)
            val argId = ArenaCell.idFromName(argName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkStore(funId, argId, elemId), 1)
          case oddEncodingType =>
            // Function updates via store constraints not happen in the oopsla19 encoding
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.storeNotInSet, elemNameEx @ NameEx(_), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.Arrays =>
            // In the arrays encoding the sets are initially empty, so elem is not a member of set implicitly
            val setId = ArenaCell.idFromName(setName)
            (mkUnchangedArray(setId), 1)
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            // In the oopsla19 encoding the sets are not initially empty, so membership has to be negated explicitly
            toExpr(tla.not(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx))))
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.storeNotInFun, elemNameEx @ NameEx(_), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            // In the arrays encoding the sets are initially empty, so elem is not a member of set implicitly
            val setId = ArenaCell.idFromName(setName)
            (mkUnchangedArray(setId), 1)
          case SMTEncoding.OOPSLA19 =>
            // In the oopsla19 encoding the sets are not initially empty, so membership has to be negated explicitly
            toExpr(tla.not((tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx)))))
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.smtMap(mapOper), NameEx(inputSetName), NameEx(resultSetName)) =>
        val mapOperDecl = mapOper match {
          case TlaBoolOper.and =>
            z3context.mkAnd().getFuncDecl
          case TlaBoolOper.or =>
            z3context.mkOr().getFuncDecl
          case _ =>
            throw new IllegalArgumentException(s"Unexpected SMT map operator of type $mapOper")
        }
        val inputSetId = ArenaCell.idFromName(inputSetName)
        val resultSetId = ArenaCell.idFromName(resultSetName)
        // The latest SSA array for resultSet contains the constraints. An updated SSA array is made to store the result
        val inputSet = cellCache(inputSetId).head._1.asInstanceOf[ArrayExpr[Sort, BoolSort]]
        val constraintsSet = cellCache(resultSetId).head._1.asInstanceOf[ArrayExpr[Sort, BoolSort]]
        val updatedResultSet = updateArrayConst(resultSetId).asInstanceOf[ArrayExpr[Sort, BoolSort]]
        // The intersection of inputSet and constraintsSet is taken and equated to updatedResultSet
        val map = z3context.mkMap(mapOperDecl, inputSet, constraintsSet)
        val eq = toEqExpr(updatedResultSet, map)
        (eq.asInstanceOf[ExprSort], 2)

      case OperEx(ApalacheInternalOper.unconstrainArray, NameEx(arrayElemName)) =>
        val arrayElemId = ArenaCell.idFromName(arrayElemName)
        updateArrayConst(arrayElemId) // A new array is declared and left unconstrained
        toExpr(tla.bool(true)) // Nothing to assert

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

  private def mkArithOp(
      ctor: (Expr[ArithSort], Expr[ArithSort]) => ArithExpr[ArithSort]
    )(a: ExprSort,
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

      case OperEx(TlaArithOper.exp, left, right) =>
        val (le, ln) = toArithExpr(left)
        val (re, rn) = toArithExpr(right)
        val mod = z3context.mkPower(le.asInstanceOf[IntExpr], re.asInstanceOf[IntExpr])
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
   * @param e
   *   an exception to throw
   * @return
   *   nothing, as an exception is unconditionally thrown
   */
  private def flushAndThrow(e: Exception): Nothing = {
    flushLogs()
    throw e
  }

  private def printStatistics(): Unit = {
    logger.info(s"Z3 statistics for context $id...")
    val entries = z3solver.getStatistics.getEntries.map(stat => {
      s"${stat.Key}=${stat.getValueString}"
    })
    logger.info(entries.mkString(",") + "\n")
  }
}

object Z3SolverContext {
  private val nextId: AtomicLong = new AtomicLong(0)

  private def createId(): Long = {
    nextId.getAndIncrement()
  }

  /**
   * The names of all parameters that are used to set the random seeds in z3.
   */
  val RANDOM_SEED_PARAMS: List[String] =
    List(
        "fp.spacer.random_seed",
        "nlsat.seed",
        "sat.random_seed",
        "sls.random_seed",
        "smt.random_seed",
    )
}

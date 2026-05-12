package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.profiler.{IdleSmtListener, SmtListener}
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.types.{tlaU => tla}
import _root_.io.github.cvc5.{CVC5ApiException, Kind, Result, Solver, Sort, Term, TermManager}

import java.io.PrintWriter
import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
 * A cvc5-backed implementation of [[SolverContext]].
 */
class Cvc5SolverContext(val config: SolverConfig) extends SolverContext {
  private val id: Long = Cvc5SolverContext.createId()
  private val logWriters: Iterable[PrintWriter] = initLogs()

  private val termManager = new TermManager()
  private val solver = new Solver(termManager)
  private val simplifier = new ConstSimplifierForSmt()
  private var smtListener: SmtListener = new IdleSmtListener()
  private var _metrics: SolverContextMetrics = SolverContextMetrics.empty

  private def encoding: SMTEncoding = config.smtEncoding
  private def defaultSmtLogic: String = encoding match {
    case SMTEncoding.OOPSLA19  => "QF_UFLIA"
    case SMTEncoding.Arrays    => "QF_AUFLIA"
    case SMTEncoding.FunArrays => "QF_UFLIA"
  }
  private def smtLogic: String =
    config.solverParams
      .get("smt.logic")
      .map(_.toString)
      .getOrElse(defaultSmtLogic)

  private var level: Int = 0
  private var maxCellIdPerContext = List(-1)

  private val cellSorts: mutable.Map[String, (Sort, Int)] =
    new mutable.HashMap[String, (Sort, Int)]
  private val cellCache: mutable.Map[Int, ListBuffer[(Term, CellT, Int)]] =
    new mutable.HashMap[Int, ListBuffer[(Term, CellT, Int)]]
  private val inCache: mutable.Map[(Int, Int), (Term, Int)] =
    new mutable.HashMap[(Int, Int), (Term, Int)]

  solver.setLogic(smtLogic)
  log(s"(set-logic $smtLogic)")
  solver.setOption("produce-models", "true")
  config.solverParams.filterNot(_._1 == "smt.logic").foreach { case (k, v) =>
    solver.setOption(k, v.toString)
  }

  override def contextLevel: Int = level

  override def push(): Unit = {
    log("(push)")
    solver.push()
    maxCellIdPerContext = maxCellIdPerContext.head +: maxCellIdPerContext
    level += 1
  }

  override def pop(): Unit = pop(1)

  override def pop(n: Int): Unit = {
    require(n >= 0, s"Expected a non-negative number of contexts to pop, found $n.")
    if (n > 0) {
      log(s"(pop $n)")
      solver.pop(n)
      maxCellIdPerContext = maxCellIdPerContext.drop(n)
      level -= n
      cellSorts.filterInPlace((_, value) => value._2 <= level)
      cellCache.foreachEntry((_, valueList) => valueList.filterInPlace(value => value._3 <= level))
      cellCache.filterInPlace((_, valueList) => valueList.nonEmpty)
      inCache.filterInPlace((_, value) => value._2 <= level)
    }
  }

  override def dispose(): Unit = {
    solver.deletePointer()
    termManager.deletePointer()
    closeLogs()
    cellCache.clear()
    inCache.clear()
    cellSorts.clear()
  }

  override def declareCell(cell: ArenaCell): Unit = {
    smtListener.onIntroCell(cell.id)

    if (maxCellIdPerContext.head >= cell.id) {
      val msg = "SMT %d: Declaring cell %d, while cell %d has been already declared. Damaged arena?"
        .format(id, cell.id, maxCellIdPerContext.head)
      throw new InternalCheckerError(msg, NullEx)
    } else {
      maxCellIdPerContext = cell.id +: maxCellIdPerContext.tail
    }

    val cellSort = getOrMkCellSort(cell.cellType)
    val cellName = cell.toString
    log(s"(declare-const $cellName $cellSort)")
    val const = termManager.mkConst(cellSort, cellName)
    cellCache += (cell.id -> ListBuffer((const, cell.cellType, level)))

    if (cell.id <= 1) {
      val expectedValue =
        if (cell.id == 0) {
          termManager.mkFalse()
        } else {
          termManager.mkTrue()
        }
      val eq = termManager.mkTerm(Kind.EQUAL, const, expectedValue)
      log(s"(assert $eq)")
      solver.assertFormula(eq)
      _metrics = _metrics.addNSmtExprs(1)
    }

    _metrics = _metrics.addNCells(1)
  }

  override def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = {
    val elemT = elem.cellType
    val setT = set.cellType
    val name = s"in_${elemT.signature}${elem.id}_${setT.signature}${set.id}"
    if (!inCache.contains((set.id, elem.id)) && encoding != SMTEncoding.Arrays) {
      smtListener.onIntroSmtConst(name)
      log(s"(declare-const $name Bool)")
      val const = termManager.mkConst(termManager.getBooleanSort, name)
      inCache += ((set.id, elem.id) -> (const, level))
      _metrics = _metrics.addNConsts(1)
    }
  }

  override def checkConsistency(arena: PureArenaAdapter): Unit = {
    val topId = arena.topCell.id
    if (maxCellIdPerContext.head > topId) {
      val msg = "SMT %d: Declaring cell %d, while cell %d has been already declared. Damaged arena?"
        .format(id, topId, maxCellIdPerContext.head)
      throw new InternalCheckerError(msg, NullEx)
    }
  }

  override def assertGroundExpr(ex: TlaEx): Unit = {
    log(s";; assert $ex")
    val (term, size) = toExpr(ex)
    _metrics = _metrics.addNSmtExprs(size)
    smtListener.onSmtAssert(ex, size)
    log(s"(assert $term)")
    solver.assertFormula(term)
  }

  override def evalGroundExpr(ex: TlaEx): TlaEx = {
    val (term, _) = toExpr(ex)
    val value = solver.getValue(term)
    if (value.isBooleanValue) {
      tla.bool(value.getBooleanValue)
    } else if (value.isIntegerValue) {
      tla.int(value.getIntegerValue)
    } else if (value.getSort.hasSymbol && value.getSort.getSymbol.startsWith("Cell_")) {
      tla.name(value.toString, TlaType1.fromTypeTag(ex.typeTag))
    } else {
      throw new SmtEncodingException(s"SMT $id: Expected an integer or Boolean, found: $value", ex)
    }
  }

  override def log(message: => String): Unit = {
    if (config.debug) {
      logWriters.foreach(_.println(message))
    }
  }

  private def initLogs(): Iterable[PrintWriter] = {
    val filePart = s"log$id.smt"
    val writers =
      (OutputManager.runDirPathOpt ++ OutputManager.customRunDirPathOpt).map(OutputManager.printWriter(_, filePart))

    if (!config.debug) {
      writers.foreach { writer =>
        writer.println("Logging is disabled (Cvc5SolverContext.debug = false). Activate with --debug.")
        writer.flush()
      }
    }

    writers
  }

  private def flushLogs(): Unit = logWriters.foreach(_.flush())

  private def closeLogs(): Unit = logWriters.foreach(_.close())

  override def sat(): Boolean = {
    log("(check-sat)")
    flushLogs()
    val result = checkSat()
    log(s";; sat = $result")
    flushLogs()
    resultToBoolean(result).getOrElse {
      val msg = s"SMT $id: cvc5 reports UNKNOWN. Maybe, your specification is outside the supported logic."
      throw new SmtEncodingException(msg, NullEx)
    }
  }

  override def satOrTimeout(timeoutSec: Int): Option[Boolean] = {
    if (timeoutSec <= 0) {
      Some(sat())
    } else {
      solver.setOption("tlimit-per", (timeoutSec * 1000).toString)
      log(s";; timeout = $timeoutSec")
      log("(check-sat)")
      flushLogs()
      val result = checkSat()
      solver.setOption("tlimit-per", "0")
      log(s";; sat = $result")
      flushLogs()
      resultToBoolean(result)
    }
  }

  override def setSmtListener(listener: SmtListener): Unit = {
    smtListener = listener
  }

  override def metrics(): SolverContextMetrics = _metrics

  private def resultToBoolean(result: Result): Option[Boolean] = {
    if (result.isSat) {
      Some(true)
    } else if (result.isUnsat) {
      Some(false)
    } else {
      None
    }
  }

  private def checkSat(): Result = {
    try {
      solver.checkSat()
    } catch {
      case err: CVC5ApiException
          if err.getMessage.contains("A non-linear term was asserted to arithmetic in a linear logic") =>
        val msg =
          s"cvc5 is using SMT logic $smtLogic, which only permits linear integer arithmetic, but the solver saw a " +
            "nonlinear arithmetic term. Re-run with --tuning-options=cvc5.smt.logic=QF_UFNIA."
        throw new SmtEncodingException(msg, NullEx)
    }
  }

  private def getInPred(setId: Int, elemId: Int): Term = {
    inCache.get((setId, elemId)) match {
      case Some((const, _)) =>
        const

      case None =>
        val setT = cellCache(setId).head._2
        val elemT = cellCache(elemId).head._2
        val name = s"in_${elemT.signature}${elemId}_${setT.signature}$setId"
        throw new IllegalStateException(
            s"SMT $id: The Boolean constant $name (set membership) is missing from the SMT context")
    }
  }

  private def getOrMkCellSort(cellType: CellT): Sort = {
    val sig = "Cell_" + cellType.signature
    cellSorts.get(sig).map(_._1).getOrElse {
      val newSort =
        cellType match {
          case CellTFrom(BoolT1) =>
            termManager.getBooleanSort

          case CellTFrom(IntT1) =>
            termManager.getIntegerSort

          case CellTFrom(SetT1(elemType)) if encoding == SMTEncoding.Arrays =>
            termManager.mkArraySort(getOrMkCellSort(CellTFrom(elemType)), termManager.getBooleanSort)

          case InfSetT(elemType) if encoding == SMTEncoding.Arrays =>
            termManager.mkArraySort(getOrMkCellSort(elemType), termManager.getBooleanSort)

          case PowSetT(domType) if encoding == SMTEncoding.Arrays =>
            termManager.mkArraySort(getOrMkCellSort(CellTFrom(domType)), termManager.getBooleanSort)

          case FinFunSetT(domType, cdmType) if encoding == SMTEncoding.Arrays =>
            val funSort = termManager.mkArraySort(mkCellElemSort(domType), mkCellElemSort(cdmType))
            termManager.mkArraySort(funSort, termManager.getBooleanSort)

          case CellTFrom(FunT1(argType, resType))
              if encoding == SMTEncoding.Arrays || encoding == SMTEncoding.FunArrays =>
            termManager.mkArraySort(getOrMkCellSort(CellTFrom(argType)), getOrMkCellSort(CellTFrom(resType)))

          case _ =>
            log(s"(declare-sort $sig 0)")
            termManager.mkUninterpretedSort(sig)
        }

      cellSorts += (sig -> (newSort, level))
      newSort
    }
  }

  private def mkCellElemSort(cellType: CellT): Sort = {
    cellType match {
      case CellTFrom(BoolT1) =>
        termManager.getBooleanSort

      case CellTFrom(IntT1) =>
        termManager.getIntegerSort

      case CellTFrom(SetT1(elemType)) if encoding == SMTEncoding.Arrays =>
        mkCellElemSort(CellTFrom(elemType))

      case PowSetT(domType) if encoding == SMTEncoding.Arrays =>
        mkCellElemSort(CellTFrom(domType))

      case FinFunSetT(argType, cdmType) if encoding == SMTEncoding.Arrays =>
        mkCellElemSort(CellTFrom(FunT1(argType.toTlaType1, cdmType.toTlaType1)))

      case CellTFrom(FunT1(argType, resType)) if encoding == SMTEncoding.Arrays || encoding == SMTEncoding.FunArrays =>
        termManager.mkArraySort(mkCellElemSort(CellTFrom(argType)), mkCellElemSort(CellTFrom(resType)))

      case _ =>
        termManager.mkUninterpretedSort("Cell_" + cellType.signature)
    }
  }

  private def toExpr(ex: TlaEx): (Term, Long) = {
    simplifier.simplifyShallow(ex) match {
      case NameEx(name) =>
        (cellCache(ArenaCell.idFromName(name)).head._1, 1)

      case ValEx(TlaBool(false)) =>
        (termManager.mkFalse(), 1)

      case ValEx(TlaBool(true)) =>
        (termManager.mkTrue(), 1)

      case ValEx(TlaInt(num)) =>
        (termManager.mkInteger(num.toString()), 1)

      case arithEx @ OperEx(_: TlaArithOper, _, _) =>
        toArithExpr(arithEx)

      case arithEx @ OperEx(_: TlaArithOper, _) =>
        toArithExpr(arithEx)

      case OperEx(TlaOper.eq, lhs, rhs) =>
        val (le, ln) = toExpr(lhs)
        val (re, rn) = toExpr(rhs)
        (termManager.mkTerm(Kind.EQUAL, le, re), 1 + ln + rn)

      case OperEx(TlaOper.ne, lhs, rhs) =>
        val (eq, n) = toExpr(tla.eql(tla.unchecked(lhs), tla.unchecked(rhs)))
        (termManager.mkTerm(Kind.NOT, eq), 1 + n)

      case OperEx(ApalacheInternalOper.distinct, args @ _*) =>
        if (args.length < 2) {
          (termManager.mkTrue(), 1)
        } else {
          val (terms, sizes) = args.map(toExpr).unzip
          (termManager.mkTerm(Kind.DISTINCT, terms.toArray), sizes.sum + 1)
        }

      case OperEx(TlaBoolOper.and, args @ _*) =>
        mkNAryBoolTerm(Kind.AND, args, identity = termManager.mkTrue())

      case OperEx(TlaBoolOper.or, args @ _*) =>
        mkNAryBoolTerm(Kind.OR, args, identity = termManager.mkFalse())

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        val (lhsCvc5, ln) = toExpr(lhs)
        val (rhsCvc5, rn) = toExpr(rhs)
        (termManager.mkTerm(Kind.IMPLIES, lhsCvc5, rhsCvc5), 1 + ln + rn)

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        val (lhsCvc5, ln) = toExpr(lhs)
        val (rhsCvc5, rn) = toExpr(rhs)
        (termManager.mkTerm(Kind.EQUAL, lhsCvc5, rhsCvc5), 1 + ln + rn)

      case OperEx(TlaControlOper.ifThenElse, cond, thenExpr, elseExpr) =>
        val (boolCond, cn) = toExpr(cond)
        val (thenCvc5, tn) = toExpr(thenExpr)
        val (elseCvc5, en) = toExpr(elseExpr)
        (termManager.mkTerm(Kind.ITE, boolCond, thenCvc5, elseCvc5), 1 + cn + tn + en)

      case OperEx(TlaBoolOper.not, e) =>
        val (term, n) = toExpr(e)
        (termManager.mkTerm(Kind.NOT, term), 1 + n)

      case OperEx(TlaSetOper.notin, elem, set) =>
        val (term, n) = toExpr(tla.in(tla.unchecked(elem), tla.unchecked(set)))
        (termManager.mkTerm(Kind.NOT, term), 1 + n)

      case OperEx(TlaSetOper.in, NameEx(elemName), NameEx(setName)) =>
        val setId = ArenaCell.idFromName(setName)
        val elemId = ArenaCell.idFromName(elemName)
        (getInPred(setId, elemId), 1)

      case OperEx(ApalacheInternalOper.selectInSet, elemNameEx @ NameEx(_), setNameEx @ NameEx(_)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx)))
          case SMTEncoding.Arrays =>
            notImplemented("Array select is not implemented in the cvc5 backend yet.")
        }

      case OperEx(ApalacheInternalOper.selectInFun, elemNameEx @ NameEx(_), funNameEx @ NameEx(_)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(funNameEx)))
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            notImplemented("Array select is not implemented in the cvc5 backend yet.")
        }

      case OperEx(ApalacheInternalOper.storeInSet, elemNameEx @ NameEx(_), setNameEx @ NameEx(_)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx)))
          case SMTEncoding.Arrays =>
            notImplemented("Array store is not implemented in the cvc5 backend yet.")
        }

      case OperEx(ApalacheInternalOper.storeNotInSet, elemNameEx @ NameEx(_), setNameEx @ NameEx(_)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.not(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx))))
          case SMTEncoding.Arrays =>
            notImplemented("Array store is not implemented in the cvc5 backend yet.")
        }

      case OperEx(ApalacheInternalOper.storeNotInFun, elemNameEx @ NameEx(_), setNameEx @ NameEx(_)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 =>
            toExpr(tla.not(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx))))
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            notImplemented("Array store is not implemented in the cvc5 backend yet.")
        }

      case OperEx(TlaSetOper.in, ValEx(TlaInt(_)), NameEx(_)) | OperEx(TlaSetOper.in, ValEx(TlaBool(_)), NameEx(_)) =>
        throw new InvalidTlaExException(s"SMT $id: Preprocessing introduced a literal inside tla.in: $ex", ex)

      case _ =>
        throw new InvalidTlaExException(s"SMT $id: Unexpected TLA+ expression: $ex", ex)
    }
  }

  private def mkNAryBoolTerm(kind: Kind, args: Seq[TlaEx], identity: Term): (Term, Long) = {
    args.length match {
      case 0 =>
        (identity, 1)
      case 1 =>
        toExpr(args.head)
      case _ =>
        val (terms, sizes) = args.map(toExpr).unzip
        (termManager.mkTerm(kind, terms.toArray), sizes.sum + 1)
    }
  }

  private def toArithExpr(ex: TlaEx): (Term, Long) = {
    def mkBinEx(kind: Kind, left: TlaEx, right: TlaEx): (Term, Long) = {
      val (le, ln) = toArithExpr(left)
      val (re, rn) = toArithExpr(right)
      (termManager.mkTerm(kind, le, re), 1 + ln + rn)
    }

    ex match {
      case ValEx(TlaInt(num)) =>
        (termManager.mkInteger(num.toString()), 1)

      case NameEx(name) if ArenaCell.isValidName(name) =>
        (cellCache(ArenaCell.idFromName(name)).head._1, 1)

      case NameEx(name) =>
        (termManager.mkConst(termManager.getIntegerSort, name), 1)

      case OperEx(TlaArithOper.lt, left, right) =>
        mkBinEx(Kind.LT, left, right)

      case OperEx(TlaArithOper.le, left, right) =>
        mkBinEx(Kind.LEQ, left, right)

      case OperEx(TlaArithOper.gt, left, right) =>
        mkBinEx(Kind.GT, left, right)

      case OperEx(TlaArithOper.ge, left, right) =>
        mkBinEx(Kind.GEQ, left, right)

      case OperEx(TlaArithOper.plus, left, right) =>
        mkBinEx(Kind.ADD, left, right)

      case OperEx(TlaArithOper.minus, left, right) =>
        mkBinEx(Kind.SUB, left, right)

      case OperEx(TlaArithOper.mult, left, right) =>
        mkBinEx(Kind.MULT, left, right)

      case OperEx(TlaArithOper.div, left, right) =>
        mkBinEx(Kind.INTS_DIVISION, left, right)

      case OperEx(TlaArithOper.mod, left, right) =>
        mkBinEx(Kind.INTS_MODULUS, left, right)

      case OperEx(TlaArithOper.exp, left, right) =>
        mkBinEx(Kind.POW, left, right)

      case OperEx(TlaArithOper.uminus, subex) =>
        val (term, n) = toArithExpr(subex)
        (termManager.mkTerm(Kind.NEG, term), 1 + n)

      case OperEx(TlaControlOper.ifThenElse, cond, thenExpr, elseExpr) =>
        val (boolCond, cn) = toExpr(cond)
        val (thenCvc5, tn) = toArithExpr(thenExpr)
        val (elseCvc5, en) = toArithExpr(elseExpr)
        (termManager.mkTerm(Kind.ITE, boolCond, thenCvc5, elseCvc5), 1 + cn + tn + en)

      case _ =>
        throw new InvalidTlaExException(s"SMT $id: Unexpected arithmetic expression: $ex", ex)
    }
  }

  private def notImplemented[A](message: String): A = {
    throw new UnsupportedOperationException(message)
  }
}

object Cvc5SolverContext {
  private val nextId: AtomicLong = new AtomicLong(0)

  private def createId(): Long = {
    nextId.getAndIncrement()
  }
}

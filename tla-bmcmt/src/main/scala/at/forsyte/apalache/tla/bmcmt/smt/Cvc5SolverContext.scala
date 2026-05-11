package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.profiler.{IdleSmtListener, SmtListener}
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.types.{tlaU => tla}
import com.typesafe.scalalogging.LazyLogging
import _root_.io.github.cvc5.{Kind, Result, Solver, Sort, Term, TermManager}

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
 * A cvc5-backed implementation of [[SolverContext]].
 */
class Cvc5SolverContext(val config: SolverConfig) extends SolverContext with LazyLogging {
  private val id: Long = Cvc5SolverContext.createId()

  private val termManager = new TermManager()
  private val solver = new Solver(termManager)
  private val simplifier = new ConstSimplifierForSmt()
  private var smtListener: SmtListener = new IdleSmtListener()
  private var _metrics: SolverContextMetrics = SolverContextMetrics.empty

  private def encoding: SMTEncoding = config.smtEncoding

  private var level: Int = 0
  private var maxCellIdPerContext = List(-1)

  private val cellSorts: mutable.Map[String, (Sort, Int)] =
    new mutable.HashMap[String, (Sort, Int)]
  private val cellCache: mutable.Map[Int, ListBuffer[(Term, CellT, Int)]] =
    new mutable.HashMap[Int, ListBuffer[(Term, CellT, Int)]]
  private val inCache: mutable.Map[(Int, Int), (Term, Int)] =
    new mutable.HashMap[(Int, Int), (Term, Int)]
  private val constantArrayCache: mutable.Map[Sort, (Term, Int)] =
    new mutable.HashMap[Sort, (Term, Int)]
  private val cellDefaults: mutable.Map[String, (Term, Int)] =
    new mutable.HashMap[String, (Term, Int)]

  solver.setOption("produce-models", "true")
  // Required for formulas containing constant arrays, which cvc5 represents as STORE_ALL terms.
  solver.setOption("arrays-exp", "true")
  config.cvc5Params.foreach { case (k, v) =>
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
      constantArrayCache.filterInPlace((_, value) => value._2 <= level)
      cellDefaults.filterInPlace((_, value) => value._2 <= level)
    }
  }

  override def dispose(): Unit = {
    solver.deletePointer()
    termManager.deletePointer()
    cellCache.clear()
    inCache.clear()
    cellSorts.clear()
    constantArrayCache.clear()
    cellDefaults.clear()
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

    if (cellSort.isArray && !cell.isUnconstrained) {
      val arrayInitializer =
        if (cell.cellType.isInstanceOf[InfSetT]) {
          termManager.mkTerm(Kind.EQUAL, const, getOrMkCellDefaultValue(cellSort, isInfiniteSet = true))
        } else {
          constantArrayCache.get(cellSort) match {
            case Some((emptyArray, _)) =>
              termManager.mkTerm(Kind.EQUAL, const, emptyArray)
            case None =>
              constantArrayCache += (cellSort -> (const, level))
              termManager.mkTerm(Kind.EQUAL, const, getOrMkCellDefaultValue(cellSort))
          }
        }
      log(s"(assert $arrayInitializer)")
      solver.assertFormula(arrayInitializer)
      _metrics = _metrics.addNSmtExprs(1)
    }

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
      logger.debug(message)
    }
  }

  override def sat(): Boolean = {
    log("(check-sat)")
    val result = solver.checkSat()
    log(s";; sat = $result")
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
      val result = solver.checkSat()
      solver.setOption("tlimit-per", "0")
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

  private def mkSelect(arrayId: Int, elemId: Int): Term = {
    val array = cellCache(arrayId).head._1
    val elem = cellCache(elemId).head._1

    termManager.mkTerm(Kind.SELECT, array, elem)
  }

  private def mkNestedSelect(outerArrayId: Int, innerArrayId: Int, elemId: Int): Term = {
    val outerArray = cellCache(outerArrayId).head._1
    val innerSelect = mkSelect(innerArrayId, elemId)

    termManager.mkTerm(Kind.SELECT, outerArray, innerSelect)
  }

  private def mkStore(arrayId: Int, indexId: Int, elemId: Int = 1): Term = {
    val (array, arrayT, _) = cellCache(arrayId).head
    val (index, indexT, _) = cellCache(indexId).head
    val (elem, elemT, _) = cellCache(elemId).head

    val oldEntry = s"${arrayT.signature}$arrayId[${indexT.signature}$indexId]"
    val newEntry = s"${elemT.signature}$elemId"
    log(s";; declare update of $oldEntry to $newEntry")

    val updatedArray = updateArrayConst(arrayId)
    val store = termManager.mkTerm(Kind.STORE, array, index, elem)

    termManager.mkTerm(Kind.EQUAL, updatedArray, store)
  }

  private def mkUnchangedArray(arrayId: Int): Term = {
    if (cellCache(arrayId).size > 1) {
      val currentArray = cellCache(arrayId).head._1
      val oldArray = cellCache(arrayId).tail.head._1
      termManager.mkTerm(Kind.EQUAL, currentArray, oldArray)
    } else if (cellCache(arrayId).size == 1) {
      termManager.mkTrue()
    } else {
      throw new IllegalStateException(
          s"SMT $id: Corrupted cellCache, $arrayId key is present, but it does not refer to any array.")
    }
  }

  private def updateArrayConst(arrayId: Int): Term = {
    val (array, arrayT, _) = cellCache(arrayId).head
    val newSSAIndex = cellCache(arrayId).size
    val updatedArrayName = array.toString.split("_").head + "_" + newSSAIndex
    val arraySort = getOrMkCellSort(arrayT)
    log(s"(declare-const $updatedArrayName $arraySort)")
    val updatedArray = termManager.mkConst(arraySort, updatedArrayName)
    cellCache += (arrayId -> cellCache(arrayId).prepend((updatedArray, arrayT, level)))
    _metrics = _metrics.addNConsts(1)
    updatedArray
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

  private def getOrMkCellDefaultValue(cellSort: Sort, isInfiniteSet: Boolean = false): Term = {
    val sig = "Cell_" + cellSort
    cellDefaults.get(sig).map(_._1).getOrElse {
      val newDefault =
        if (cellSort.isBoolean) {
          termManager.mkFalse()
        } else if (cellSort.isInteger) {
          termManager.mkInteger("0")
        } else if (cellSort.isArray && isInfiniteSet) {
          termManager.mkConstArray(cellSort, termManager.mkTrue())
        } else if (
            cellSort.isArray && encoding == SMTEncoding.Arrays && hasValueDefault(cellSort.getArrayElementSort)
        ) {
          // In FunArrays, function updates create STORE terms over these defaults. With constant-array defaults,
          // cvc5 1.3.4 can throw during checkSat with "Array theory solver does not yet support write-chains
          // connecting two different constant arrays", so FunArrays use a cached fresh array constant instead.
          termManager.mkConstArray(cellSort, getOrMkCellDefaultValue(cellSort.getArrayElementSort))
        } else {
          log(s"(declare-const $sig $cellSort)")
          termManager.mkConst(cellSort, sig)
        }

      cellDefaults += (sig -> (newDefault, level))
      newDefault
    }
  }

  private def hasValueDefault(cellSort: Sort): Boolean = {
    // cvc5 mkConstArray requires the default element to be a value. Booleans, integers, and recursively constant
    // arrays over value defaults are OK. Uninterpreted cell defaults like Cell_Cell_Si are not values, so we use a
    // fresh unconstrained array constant instead. The default is still stable because it is cached by sort, but the
    // encoding is weaker than Z3's fixed-value constant arrays: unstored entries are arbitrary.
    cellSort.isBoolean || cellSort.isInteger || cellSort.isArray && hasValueDefault(cellSort.getArrayElementSort)
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

      case OperEx(ApalacheInternalOper.selectInSet, elemNameEx @ NameEx(elemName), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx)))
          case SMTEncoding.Arrays =>
            val setId = ArenaCell.idFromName(setName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkSelect(setId, elemId), 1)
        }

      case OperEx(ApalacheInternalOper.selectInFun, elemNameEx @ NameEx(elemName), funNameEx @ NameEx(funName)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(funNameEx)))
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            val funId = ArenaCell.idFromName(funName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkSelect(funId, elemId), 1)
        }

      case OperEx(ApalacheInternalOper.selectInSet,
              OperEx(ApalacheInternalOper.selectInFun, NameEx(elemName), NameEx(funName)), NameEx(setName)) =>
        encoding match {
          case SMTEncoding.Arrays =>
            val set2Id = ArenaCell.idFromName(setName)
            val set1Id = ArenaCell.idFromName(funName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkNestedSelect(set2Id, set1Id, elemId), 1)
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.storeInSet, elemNameEx @ NameEx(elemName), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx)))
          case SMTEncoding.Arrays =>
            val setId = ArenaCell.idFromName(setName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkStore(setId, elemId), 1)
        }

      case OperEx(ApalacheInternalOper.storeInSet, NameEx(elemName), NameEx(funName), NameEx(argName)) =>
        encoding match {
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            val funId = ArenaCell.idFromName(funName)
            val argId = ArenaCell.idFromName(argName)
            val elemId = ArenaCell.idFromName(elemName)
            (mkStore(funId, argId, elemId), 1)
          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case OperEx(ApalacheInternalOper.storeNotInSet, elemNameEx @ NameEx(_), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            toExpr(tla.not(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx))))
          case SMTEncoding.Arrays =>
            val setId = ArenaCell.idFromName(setName)
            (mkUnchangedArray(setId), 1)
        }

      case OperEx(ApalacheInternalOper.storeNotInFun, elemNameEx @ NameEx(_), setNameEx @ NameEx(setName)) =>
        encoding match {
          case SMTEncoding.OOPSLA19 =>
            toExpr(tla.not(tla.in(tla.unchecked(elemNameEx), tla.unchecked(setNameEx))))
          case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
            val setId = ArenaCell.idFromName(setName)
            (mkUnchangedArray(setId), 1)
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

}

object Cvc5SolverContext {
  private val nextId: AtomicLong = new AtomicLong(0)

  private def createId(): Long = {
    nextId.getAndIncrement()
  }
}

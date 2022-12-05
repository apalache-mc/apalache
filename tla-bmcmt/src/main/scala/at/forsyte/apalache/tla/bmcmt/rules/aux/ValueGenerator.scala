package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.FixedElemPtr
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps.constrainRelationArgs
import at.forsyte.apalache.tla.bmcmt.types.{CellT, CellTFrom}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.{tla => tlaLegacy}
import at.forsyte.apalache.tla.types.tla
import scalaz.unused

import scala.collection.immutable.{SortedMap, SortedSet}

/**
 * This class generates symbolic data structures whose width is bounded with `bound`
 *
 * @param rewriter
 *   a rewriter
 * @param bound
 *   an upper bound on the size of the generated structures
 * @author
 *   Igor Konnov
 */
class ValueGenerator(rewriter: SymbStateRewriter, bound: Int) {
  private val proto = new ProtoSeqOps(rewriter)
  private val recordAndVariantOps = new RecordAndVariantOps(rewriter)

  def gen(state: SymbState, resultType: TlaType1): SymbState = {
    rewriter.solverContext.log(s"; GEN $resultType up to $bound {")
    val nextState =
      resultType match {
        case IntT1 | BoolT1 | StrT1 | ConstT1(_) =>
          // For the moment, we do not distinguish between ConstT1 and StrT1.
          // When issue #570 is fixed, we should come back to it.
          genBasic(state, resultType)

        case SetT1(elemType) =>
          genSet(state, elemType)

        case SeqT1(elemType) =>
          genSeq(state, elemType)

        case rt @ RecT1(_) =>
          genRecord(state, rt)

        case RecRowT1(RowT1(fieldTypes, None)) =>
          genRowRecord(state, fieldTypes)

        case VariantT1(RowT1(options, None)) =>
          genVariant(state, options)

        case tt @ TupT1(_ @_*) =>
          genTuple(state, tt)

        case ft @ FunT1(_, _) =>
          genFun(state, ft)

        case tp =>
          throw new RewriterException(s"Apalache!Gen did not expect the type $tp", state.ex)
      }

    rewriter.solverContext.log(s"; } GEN $resultType up to $bound")

    nextState
  }

  private def genBasic(state: SymbState, basicType: TlaType1): SymbState = {
    val nextState = state.updateArena(a => a.appendCell(basicType))
    nextState.setRex(nextState.arena.topCell.toNameEx.withTag(Typed(basicType)))
  }

  private def genRecord(state: SymbState, recordType: RecT1): SymbState = {
    // create the record domain
    val (domArena, domCell) =
      rewriter.recordDomainCache.create(state.arena, (recordType.fieldTypes.keySet, SortedSet.empty))
    // create the record cell
    var nextState = state.setArena(domArena.appendCell(recordType))
    val recCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.setDom(recCell, domCell))
    // convert the values to a list, so we don't have a lazy stream
    val elemTypes = recordType.fieldTypes.values.toList
    val elemCells =
      elemTypes
        .map { elemType =>
          nextState = gen(nextState, elemType)
          nextState.asCell
        }
        .map { FixedElemPtr(_, true) }
    nextState = nextState.updateArena(a => a.appendHasNoSmt(recCell, elemCells: _*))
    nextState.setRex(recCell.toNameEx.withTag(Typed(recordType)))
  }

  private def genRowRecord(state: SymbState, fieldTypes: SortedMap[String, TlaType1]): SymbState = {
    // create the record cell
    val recordT = RecRowT1(RowT1(fieldTypes, None))
    var nextState = state.updateArena(_.appendCell(recordT))
    val recCell = nextState.arena.topCell
    // convert the values to a list, so we don't have a lazy stream
    val elemCells =
      fieldTypes.values.toList
        .map { elemType =>
          nextState = gen(nextState, elemType)
          nextState.asCell
        }
        .map { FixedElemPtr(_, true) }
    nextState = nextState.updateArena(a => a.appendHasNoSmt(recCell, elemCells: _*))
    nextState.setRex(recCell.toNameEx.withTag(Typed(CellTFrom(recordT))))
  }

  private def genVariant(state: SymbState, options: SortedMap[String, TlaType1]): SymbState = {
    // generate the tag name
    var nextState = genBasic(state, StrT1)
    val tagCell = nextState.asCell
    // assert that one of the options is selected
    val tags = options.keys.map { name =>
      nextState = recordAndVariantOps.getOrCreateVariantTag(nextState, name)
      tla.eql(nextState.asCell.toBuilder, tagCell.toBuilder)
    }.toSeq
    rewriter.solverContext.assertGroundExpr(tla.or(tags: _*))
    // generate the possible values
    val namedValues = options.map { case (key, tt) =>
      nextState = gen(nextState, tt)
      (key, nextState.asCell)
    }
    // create a variant cell and connect values to it
    val variantFields = namedValues + (RecordAndVariantOps.variantTagField -> tagCell)
    nextState = nextState.updateArena(_.appendCell(VariantT1(RowT1(options, None))))
    val variantCell = nextState.arena.topCell
    // add the fields in the order of their names
    for (fieldCell <- variantFields.valuesIterator) {
      nextState = nextState.updateArena(_.appendHasNoSmt(variantCell, FixedElemPtr(fieldCell, true)))
    }

    nextState.setRex(variantCell.toNameEx)
  }

  private def genTuple(state: SymbState, tupleType: TupT1): SymbState = {
    var nextState = state.updateArena(a => a.appendCell(tupleType))
    val tupleCell = nextState.arena.topCell
    // convert the values to a list, so we don't have a lazy stream
    val elemCells =
      tupleType.elems
        .map { elemType =>
          nextState = gen(nextState, elemType)
          nextState.asCell
        }
        .map { FixedElemPtr(_, true) }
    nextState = nextState.updateArena(a => a.appendHasNoSmt(tupleCell, elemCells: _*))
    nextState.setRex(tupleCell.toNameEx.withTag(Typed(tupleType)))
  }

  private def genSet(state: SymbState, elemType: TlaType1): SymbState = {
    var nextState = state
    var elems: List[ArenaCell] = Nil
    for (_ <- 1 to bound) {
      nextState = gen(nextState, elemType)
      elems = nextState.asCell :: elems
    }
    val setType = CellT.fromType1(SetT1(elemType))
    nextState = nextState.updateArena(a => a.appendCellOld(setType))
    val setCell = nextState.arena.topCell
    nextState = nextState.updateArena(a => a.appendHas(setCell, elems.map { FixedElemPtr(_, true) }: _*))
    // In the arrays encoding, set membership constraints are not generated in appendHas, so we add them below
    if (rewriter.solverContext.config.smtEncoding == SMTEncoding.Arrays) {
      for (elem <- elems) {
        nextState = nextState.updateArena(_.appendCell(BoolT1))
        val pred = nextState.arena.topCell.toNameEx
        // TODO: when #1916 is closed, remove tlaLegacy and use tla directly
        val storeElem = tlaLegacy.apalacheStoreInSet(elem.toNameEx, setCell.toNameEx).typed(SetT1(elemType))
        val notStoreElem = tlaLegacy.apalacheStoreNotInSet(elem.toNameEx, setCell.toNameEx).typed(SetT1(elemType))
        // elem is added to setCell based on the unconstrained predicate pred
        val ite = tlaLegacy.ite(pred, storeElem, notStoreElem).typed(SetT1(elemType))
        rewriter.solverContext.assertGroundExpr(ite)
      }
    }
    nextState.setRex(setCell.toNameEx.withTag(Typed(SetT1(elemType))))
  }

  private def genSeq(state: SymbState, elemType: TlaType1): SymbState = {
    // initialize the proto sequence with the elements
    def genElem(s: SymbState, @unused indexBase1: Int): (SymbState, ArenaCell) = {
      // ignore indexBase1, as it is irrelevant
      val ns = gen(s, elemType)
      (ns, ns.asCell)
    }

    var nextState = proto.make(state, bound, genElem)
    val newProtoSeq = nextState.asCell
    // create the cell to store length
    nextState = genBasic(nextState, IntT1)
    val len = nextState.asCell
    // assert that 0 <= len /\ len <= bound
    rewriter.solverContext.assertGroundExpr(tla.le(len.toBuilder, tla.int(bound)))
    rewriter.solverContext.assertGroundExpr(tla.ge(len.toBuilder, tla.int(0)))
    // create the sequence out of the proto sequence and its length
    proto.mkSeq(nextState, SeqT1(elemType), newProtoSeq, nextState.asCell)
  }

  private def genFun(state: SymbState, funType: FunT1): SymbState = {
    var nextState = state
    var pairs: List[ArenaCell] = Nil
    // generate a sequence of pairs <<x, y>> that will represent the function
    for (_ <- 1 to bound) {
      nextState = gen(nextState, TupT1(funType.arg, funType.res))
      pairs = nextState.asCell :: pairs
    }

    // create a function cell
    nextState = nextState.updateArena(_.appendCell(funType))
    val funCell = nextState.arena.topCell

    rewriter.solverContext.config.smtEncoding match {
      case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
        // create a relation cell
        nextState = nextState.updateArena(_.appendCellNoSmt(CellTFrom(SetT1(TupT1(funType.arg, funType.res)))))
        val relationCell = nextState.arena.topCell
        nextState = nextState.updateArena(_.appendHasNoSmt(relationCell, pairs.map { FixedElemPtr(_, true) }: _*))
        nextState = nextState.updateArena(_.setCdm(funCell, relationCell))

        val domainCells = pairs.map(pair => nextState.arena.getHas(pair)(0))
        val rangeCells = pairs.map(pair => nextState.arena.getHas(pair)(1))

        nextState = nextState.updateArena(_.appendCell(SetT1(funType.arg)))
        val domainCell = nextState.arena.topCell
        nextState = nextState.updateArena(_.appendHas(domainCell, domainCells.map { FixedElemPtr(_, true) }: _*))
        // In the arrays encoding, set membership constraints are not generated in appendHas, so we add them below
        for (domainElem <- domainCells) {
          // TODO: when #1916 is closed, remove tlaLegacy and use tla directly
          val inExpr = tlaLegacy.apalacheStoreInSet(domainElem.toNameEx, domainCell.toNameEx).typed(BoolT1)
          rewriter.solverContext.assertGroundExpr(inExpr)
        }
        nextState = nextState.updateArena(_.setDom(funCell, domainCell))
        // For the decoder to work, the relation's arguments may need to be equated to the domain elements
        nextState = constrainRelationArgs(nextState, rewriter, domainCell, relationCell)

        def addCellCons(domElem: ArenaCell, rangeElem: ArenaCell): Unit = {
          // TODO: when #1916 is closed, remove tlaLegacy and use tla directly
          val inDomain = tlaLegacy.apalacheSelectInFun(domElem.toNameEx, domainCell.toNameEx).typed(BoolT1)
          val inRange =
            tlaLegacy.apalacheStoreInFun(rangeElem.toNameEx, funCell.toNameEx, domElem.toNameEx).typed(BoolT1)
          val notInRange = tlaLegacy.apalacheStoreNotInFun(domElem.toNameEx, funCell.toNameEx).typed(BoolT1)
          // function updates are guarded by the inDomain predicate
          val ite = tlaLegacy.ite(inDomain, inRange, notInRange).as(BoolT1)
          rewriter.solverContext.assertGroundExpr(ite)
        }

        // add SMT constraints
        for ((domElem, rangeElem) <- domainCells.zip(rangeCells))
          addCellCons(domElem, rangeElem)

      case SMTEncoding.OOPSLA19 =>
        // create a relation cell
        nextState = nextState.updateArena(_.appendCell(SetT1(TupT1(funType.arg, funType.res))))
        val relationCell = nextState.arena.topCell
        // we just add the pairs, but do not restrict their membership, as the generator is free to produce a set
        // that is an arbitrary subset of the pairs
        nextState = nextState.updateArena(_.appendHas(relationCell, pairs.map { FixedElemPtr(_, true) }: _*))

        nextState = nextState.updateArena(_.setCdm(funCell, relationCell))
        // Require that if two arguments belong to the domain, they are distinct.
        // This will guarantee that we define a function, not an arbitrary relation.
        // Note that we cannot simply require that all arguments are distinct,
        // as there may be not enough values in the universe to guarantee that.
        for ((p1, i1) <- pairs.zipWithIndex) {
          for ((p2, i2) <- pairs.zipWithIndex) {
            if (i1 < i2) {
              // get the arguments that are associated with the pairs
              val a1 = nextState.arena.getHas(p1).head
              val a2 = nextState.arena.getHas(p2).head
              // if two pairs belong to the relation, their arguments must be unequal
              nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((a1, a2)))
              val not1 = tla.not(tla.in(p1.toBuilder, relationCell.toBuilder))
              val not2 = tla.not(tla.in(p2.toBuilder, relationCell.toBuilder))
              val neq = tla.not(tla.eql(a1.toBuilder, a2.toBuilder))
              rewriter.solverContext.assertGroundExpr(tla.or(not1, not2, neq))
            }
          }
        }

      case oddEncodingType =>
        throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
    }

    nextState.setRex(funCell.toNameEx.withTag(Typed(funType)))
  }
}

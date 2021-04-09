package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.{CellT, FinSetT, IntT, TupleT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.SortedSet

/**
 * This class generates symbolic data structures whose width is bounded with `bound`
 *
 * @param rewriter a rewriter
 * @param bound    an upper bound on the size of the generated structures
 * @author Igor Konnov
 */
class ValueGenerator(rewriter: SymbStateRewriter, bound: Int) {
  def gen(state: SymbState, resultType: TlaType1): SymbState = {
    rewriter.solverContext.log(s"; GEN $resultType up to $bound {")
    val nextState =
      resultType match {
        case IntT1() | BoolT1() | StrT1() | ConstT1(_) =>
          // For the moment, we do not distinguish between ConstT1 and StrT1.
          // When issue #570 is fixed, we should come back to it.
          genBasic(state, resultType)

        case SetT1(elemType) =>
          genSet(state, elemType)

        case SeqT1(elemType) =>
          genSeq(state, elemType)

        case rt @ RecT1(_) =>
          genRecord(state, rt)

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
    val nextState = state.updateArena(a => a.appendCell(CellT.fromType1(basicType)))
    nextState.setRex(nextState.arena.topCell.toNameEx.withTag(Typed(basicType)))
  }

  private def genRecord(state: SymbState, recordType: RecT1): SymbState = {
    // create the record domain
    val (domArena, domCell) =
      rewriter.recordDomainCache.create(state.arena, (recordType.fieldTypes.keySet, SortedSet.empty))
    // create the record cell
    var nextState = state.setArena(domArena.appendCell(CellT.fromType1(recordType)))
    val recCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.setDom(recCell, domCell))
    // convert the values to a list, so we don't have a lazy stream
    val elemTypes = recordType.fieldTypes.values.toList
    val elemCells =
      elemTypes map { elemType =>
        nextState = gen(nextState, elemType)
        nextState.asCell
      }
    nextState = nextState.updateArena(a => a.appendHasNoSmt(recCell, elemCells: _*))
    nextState.setRex(recCell.toNameEx.withTag(Typed(recordType)))
  }

  private def genTuple(state: SymbState, tupleType: TupT1): SymbState = {
    var nextState = state.updateArena(a => a.appendCell(CellT.fromType1(tupleType)))
    val tupleCell = nextState.arena.topCell
    // convert the values to a list, so we don't have a lazy stream
    val elemCells =
      tupleType.elems map { elemType =>
        nextState = gen(nextState, elemType)
        nextState.asCell
      }
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
    val setType = FinSetT(CellT.fromType1(elemType))
    nextState = nextState.updateArena(a => a.appendCell(setType))
    val setCell = nextState.arena.topCell
    nextState = nextState.updateArena(a => a.appendHas(setCell, elems: _*))
    nextState.setRex(setCell.toNameEx.withTag(Typed(SetT1(elemType))))
  }

  private def genSeq(state: SymbState, elemType: TlaType1): SymbState = {
    // The following code is following pretty much TupleOrSeqCtorRule.
    // Sequences are much simpler than functions because all the elements in its domain are unique.

    // Create a sequence cell.
    val seqType = CellT.fromType1(SeqT1(elemType))
    var nextState = state.updateArena(_.appendCell(seqType))
    val seq = nextState.arena.topCell

    // generate bound elements
    var elems: List[ArenaCell] = Nil
    for (_ <- 1 to bound) {
      nextState = gen(nextState, elemType)
      elems = nextState.asCell :: elems
    }

    // connect N + 2 elements to seqT: the start (>= 0), the end (< bound), and the sequence of values
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.int(0).typed()))
    val start = nextState.asCell
    nextState = nextState.updateArena(_.appendCell(IntT()))
    val end = nextState.arena.topCell
    val types = Map("i" -> IntT1(), "b" -> BoolT1())
    rewriter.solverContext.assertGroundExpr(tla.lt(end.toNameEx ? "i", tla.int(bound)).typed(types, "b"))
    rewriter.solverContext.assertGroundExpr(tla.ge(end.toNameEx ? "i", tla.int(0)).typed(types, "b"))
    nextState = nextState.updateArena(_.appendHasNoSmt(seq, start +: end +: elems: _*))
    // we do not add SMT constraints as they are not important
    nextState.setRex(seq.toNameEx)
  }

  private def genFun(state: SymbState, funType: FunT1): SymbState = {
    var nextState = state
    var pairs: List[ArenaCell] = Nil
    // generate a sequence of pairs <<x, y>> that will represent the function
    for (_ <- 1 to bound) {
      nextState = gen(nextState, TupT1(funType.arg, funType.res))
      pairs = nextState.asCell :: pairs
    }
    // create a relation cell
    val argT = CellT.fromType1(funType.arg)
    val resT = CellT.fromType1(funType.res)
    nextState = nextState.updateArena(_.appendCell(FinSetT(TupleT(Seq(argT, resT)))))
    val relationCell = nextState.arena.topCell
    // we just add the pairs, but do not restrict their membership, as the generator is free to produce a set
    // that is an arbitrary subset of the pairs
    nextState = nextState.updateArena(_.appendHas(relationCell, pairs: _*))
    // create a function cell
    nextState = nextState.updateArena(_.appendCell(CellT.fromType1(funType)))
    val funCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.setCdm(funCell, relationCell))
    // Require that if two arguments belong to the domain, they are distinct.
    val types = Map("p" -> TupT1(funType.arg, funType.res), "R" -> SetT1(TupT1(funType.arg, funType.res)),
        "a" -> funType.arg, "b" -> BoolT1())
    for ((p1, i1) <- pairs.zipWithIndex) {
      for ((p2, i2) <- pairs.zipWithIndex) {
        if (i1 < i2) {
          // get the arguments that are associated with the pairs
          val a1 = nextState.arena.getHas(p1).head
          val a2 = nextState.arena.getHas(p2).head
          // if two pairs belong to the relation, their arguments must be unequal
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((a1, a2)))
          val not1 = tla
            .not(tla.in(p1.toNameEx ? "p", relationCell.toNameEx ? "R") ? "b")
            .typed(types, "b")
          val not2 = tla
            .not(tla.in(p2.toNameEx ? "p", relationCell.toNameEx ? "R") ? "b")
            .typed(types, "b")
          val neq = tla
            .not(tla.eql(a1.toNameEx ? "a", a2.toNameEx ? "a") ? "b")
            .typed(types, "b")
          rewriter.solverContext.assertGroundExpr(tla.or(not1, not2, neq).typed(BoolT1()))
        }
      }
    }
    // This will guarantee that we define a function, not an arbitrary relation.
    // Note that we cannot simply require that all arguments are distinct,
    // as there may be not enough values in the universe to guarantee that.
    nextState.setRex(funCell.toNameEx.withTag(Typed(funType)))
  }
}

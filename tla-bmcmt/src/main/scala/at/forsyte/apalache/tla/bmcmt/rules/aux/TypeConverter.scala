package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.{CellT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.bmcmt.{SymbState, SymbStateRewriter}

/**
  * TypeConvertor takes a cell of one type and converts it to a cell of another type, when possible.
  * For instance, a cell of type PowSetT(t) can be converted to FinSetT(t) by expanding the powerset.
  * These conversions typically produce lots of constraints, but we do not have any choice, if we want
  * to support the whole of TLA+.
  *
  * @author Igor Konnov
  */
class TypeConverter(rewriter: SymbStateRewriter) {
  private val powSetCtor = new PowSetCtor(rewriter)

  def convert(state: SymbState, targetType: CellT): SymbState = {
    val sourceCell = state.asCell
    (sourceCell.cellType, targetType) match {
      case (PowSetT(elemT1), FinSetT(elemT2)) if elemT1 == elemT2 =>
        powSetCtor.confringo(state, state.arena.getDom(sourceCell))

        // TODO: convert [S -> T] to an explicit set of functions? (though it's crazy)

      case _ =>
        throw new NotImplementedError("Type conversion from %s to %s is not supported"
          .format(sourceCell.cellType, targetType))
    }
  }
}

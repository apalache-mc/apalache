package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.{BuilderEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Given a SMT encoding, this class produces set access and set update operators.
 *
 * @author Rodrigo Otoni
 */
class InOpFactory(smtEncoding: String) {

  /**
   * @param elemEx the element selected
   * @param setEx  the set being accessed
   * @return       a BuilderEx that can be used to check set membership
   */
  def mkAccessOp(elemEx: TlaEx, setEx: TlaEx): BuilderEx = {
    smtEncoding match {
      case "arrays" => tla.apalacheSelectInSet(elemEx, setEx)
      case _        => tla.in(elemEx, setEx)
    }
  }

  /**
   * @param elem the element selected
   * @param set  the set being accessed
   * @return     a BuilderEx that can be used to check set membership
   */
  def mkAccessOp(elem: ArenaCell, set: ArenaCell): BuilderEx = {
    mkAccessOp(elem.toNameEx, set.toNameEx)
  }

  /**
   * @param elemEx the element selected
   * @param setEx  the set being updated
   * @return       a BuilderEx that can be used to update set membership
   */
  def mkUpdateOp(elemEx: TlaEx, setEx: TlaEx): BuilderEx = {
    smtEncoding match {
      case "arrays" => tla.apalacheStoreInSet(elemEx, setEx)
      case _        => tla.in(elemEx, setEx)
    }
  }

  /**
   * @param elem the element selected
   * @param set  the set being updated
   * @return     a BuilderEx that can be used to update set membership
   */
  def mkUpdateOp(elem: ArenaCell, set: ArenaCell): BuilderEx = {
    mkUpdateOp(elem.toNameEx, set.toNameEx)
  }

  /**
   * @param elemEx the element selected, which will not be added to the set
   * @param setEx  the set selected
   * @return       a BuilderEx that can be used to update set membership
   */
  def mkUnchangedOp(elemEx: TlaEx, setEx: TlaEx): BuilderEx = {
    smtEncoding match {
      case "arrays" => tla.apalacheUnchangedSet(setEx) // Unless explicitly added, elemEx is not part of the set
      case _        => tla.not(tla.in(elemEx, setEx))
    }
  }

  /**
   * @param elem the element selected, which will not be added to the set
   * @param set  the set selected
   * @return     a BuilderEx that can be used to update set membership
   */
  def mkUnchangedOp(elem: ArenaCell, set: ArenaCell): BuilderEx = {
    mkUnchangedOp(elem.toNameEx, set.toNameEx)
  }
}

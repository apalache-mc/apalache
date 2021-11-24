package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.{BuilderEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Given a SMT encoding, this class produces set read and set write operators.
 *
 * @author Rodrigo Otoni
 */
class SetMembershipFactory(smtEncoding: String) {

  /**
   * @param elemEx the element selected
   * @param setEx  the set being accessed
   * @return       a BuilderEx that can be used to check set membership
   */
  def mkReadMem(elemEx: TlaEx, setEx: TlaEx): BuilderEx = {
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
  def mkReadMem(elem: ArenaCell, set: ArenaCell): BuilderEx = {
    mkReadMem(elem.toNameEx, set.toNameEx)
  }

  /**
   * @param elemEx the element selected
   * @param setEx  the set being updated
   * @return       a BuilderEx that can be used to update set membership
   */
  def mkWriteMem(elemEx: TlaEx, setEx: TlaEx): BuilderEx = {
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
  def mkWriteMem(elem: ArenaCell, set: ArenaCell): BuilderEx = {
    mkWriteMem(elem.toNameEx, set.toNameEx)
  }

  /**
   * @param elemEx the element selected, which will not be a part of the set
   * @param setEx  the set selected
   * @return       a BuilderEx that can be used to update set membership
   */
  def mkNotMem(elemEx: TlaEx, setEx: TlaEx): BuilderEx = {
    smtEncoding match {
      case "arrays" => tla.apalacheUnchangedSet(setEx) // Unless explicitly added, elemEx is not part of the set
      case _        => tla.not(tla.in(elemEx, setEx))
    }
  }

  /**
   * @param elem the element selected, which will not be a part of the set
   * @param set  the set selected
   * @return     a BuilderEx that can be used to update set membership
   */
  def mkNotMem(elem: ArenaCell, set: ArenaCell): BuilderEx = {
    mkNotMem(elem.toNameEx, set.toNameEx)
  }
}

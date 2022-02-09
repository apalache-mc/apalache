package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts
import at.forsyte.apalache.tla.lir.values.TlaPredefSet

package object vmt {
  type BoolTermRule = FormulaRule[StandardSorts.BoolSort]
  type BoolRewriter = Rewriter[StandardSorts.BoolSort]
}

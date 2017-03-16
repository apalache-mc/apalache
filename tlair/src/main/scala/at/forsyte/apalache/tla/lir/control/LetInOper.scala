package at.forsyte.apalache.tla.lir.control

import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.oper.{FixedArity, Interpretation, OperArity}

/**
  * The LET A_1 == e_1, ..., A_k = e_k in B. Let-In is a very special operator, as it introduces
  * new operator definitions. At the moment, we store only the body as an argument, whereas the actual
  * definitions are accessible via the field defs. In the future, this might change.
  */
class LetInOper(val defs: List[TlaOperDecl]) extends TlaControlOper {
  override val name: String = "LET-IN"
  override val arity: OperArity = FixedArity(1)
  override val interpretation: Interpretation.Value = Interpretation.Predefined
}

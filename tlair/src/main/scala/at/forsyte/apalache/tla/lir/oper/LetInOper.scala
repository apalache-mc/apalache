package at.forsyte.apalache.tla.lir.oper

import at.forsyte.apalache.tla.lir.TlaOperDecl

/**
  * The LET A_1 == e_1, ..., A_k = e_k in B. Let-In is a very special operator, as it introduces
  * new operator definitions. At the moment, we store only the body as an argument, whereas the actual
  * definitions are accessible via the field defs. In the future, this might change.
  *
  * TODO: Igor @ 02.07.2019: remove this operator and introduce LetInEx(_: TlaOperDecl) extends TlaEx.
  * See: https://github.com/konnov/apalache/issues/14
  */
class LetInOper(val defs: List[TlaOperDecl]) extends TlaControlOper {
  override val name: String = "LET-IN"
  override val arity: OperArity = FixedArity(1)
  override val interpretation: Interpretation.Value = Interpretation.Predefined

  override def equals( obj : scala.Any ) : Boolean = obj match {
    case letIn: LetInOper => defs == letIn.defs
    case _ => false
  }
}

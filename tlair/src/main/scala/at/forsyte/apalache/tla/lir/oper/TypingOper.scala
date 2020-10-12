package at.forsyte.apalache.tla.lir.oper

/**
  * The operators defined in the module Typing.tla.
  *
  * @author Igor Konnov
 */
abstract class TypingOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object TypingOper {
  /**
    * Assume that a constant or a state variable has the type type_str.
    * This operator should be used in the top-level operator TypeAssumptions.
    * The first argument should be NameEx(_), and the second argument should be ValEx(TlaStr(_)).
    */
  object assumeType extends TypingOper {
    override def name: String = "Typing!AssumeType"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (100, 100)
  }

  /**
    * Annotate an operator body (or the body of a recursive function) with a type.
    * The first argument should be ValEx(TlaStr(_)), and the second argument should be TlaEx (operator body).
    */
  object withType extends TypingOper {
    override def name: String = "Typing!:>"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (100, 100)
  }

}




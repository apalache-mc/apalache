package at.forsyte.apalache.tla.lir.oper

/**
  * Created by jkukovec on 11/16/16.
  */

abstract class TlaArithOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaArithOper {

  val sum = new TlaArithOper {
    override val arity = AnyArity() // Empty sum = 0
    override val name = "SUM"
  }

  val plus = new TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "+"
  }

  val uminus = new TlaArithOper {
    override val arity = FixedArity(1)
    override val name = "unary-"
  }

  val minus = new TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "-"
  }

  val prod = new TlaArithOper {
    override def arity = AnyArity()   // empty prod = 1
    override def name = "PROD"
  }

  val mult = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override def name: String = "*"
  }

  val exp = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override def name: String = "^"
  }

  val dotdot = new TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "_.._"
  }

}

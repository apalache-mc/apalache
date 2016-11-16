package at.forsyte.apalache.tla.lir.oper

/**
  * Created by jkukovec on 11/16/16.
  */

abstract class TlaArithmeticOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaArithmeticOper {

  val sum = new TlaArithmeticOper {
    override val arity = AnyArity() // Empty sum = 0
    override val name = "SIGMA"
  }

  val plus = new TlaArithmeticOper {
    override val arity = FixedArity(2)
    override val name = "+"
  }

  val uminus = new TlaArithmeticOper {
    override val arity = FixedArity(1)
    override val name = "unary-"
  }

  val minus = new TlaArithmeticOper {
    override val arity = FixedArity(2)
    override val name = "-"
  }

  val seqprod = new TlaArithmeticOper {
    override def arity = AnyArity()   // empty prod = 1
    override def name = "PI"
  }

  val prod = new TlaArithmeticOper {
    override def arity: OperArity = FixedArity(2)
    override def name: String = "*"
  }

  val exp = new TlaArithmeticOper {
    override def arity: OperArity = FixedArity(2)
    override def name: String = "^"
  }

}

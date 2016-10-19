package at.forsyte.apalache.tla.lir.oper

/**
 * Function operators.
 */
abstract class TlaFunOper extends TlaOper {
  override def level: Level.Value = Level.State
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaFunOper {
  /** f[e] */
  val app = new TlaFunOper {
    override val arity: OperArity = FixedArity(2)
    override val name: String = "fun-app"
  }

  /** DOMAIN f */
  val domain = new TlaFunOper {
    override val arity: OperArity = FixedArity(1)
    override val name: String = "DOMAIN"
  }

  /** [ x \in S |-> e ] */
  val funDef = new TlaFunOper {
    override def arity: OperArity = FixedArity(3)

    override def name: String = "fun-def"
  }

  /** [f EXCEPT ![i1] = e_1, ![i_2] = e_2, ..., ![i_k] = e_k] */
  val except = new TlaFunOper {
    override def arity: OperArity = AnyArity()

    override def name: String = "EXCEPT"
  }
}

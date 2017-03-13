package at.forsyte.apalache.tla.lir.oper

/**
  * Boolean operators.
  *
  * Rename it to TlaLogicOper to make it more consistent?
  */
abstract class TlaBoolOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaBoolOper {
  val and = new TlaBoolOper {
    override def arity = AnyArity()

    override def name = "/\\"
  }

  val or = new TlaBoolOper {
    override def arity: OperArity = AnyArity()

    override def name: String = "\\/"
  }

  val not = new TlaBoolOper {
    override def arity: OperArity = FixedArity(1)

    override def name: String = "~"
  }

  val implies = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override def name: String = "=>"
  }

  val equiv = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override def name: String = "<=>"
  }

  /** \forall x \in S : p */
  val forall = new TlaBoolOper {
    override def arity: OperArity = FixedArity(3)

    override def name: String = "\\A3"
  }

  /** \forall x : p */
  val forallUnbounded = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override def name: String = "\\A2"
  }

  /** \exists x \in S : p */
  val exists = new TlaBoolOper {
    override def arity: OperArity = FixedArity(3)

    override def name: String = "\\E3"
  }

  /** \exists x : p */
  val existsUnbounded = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override def name: String = "\\E2"
  }
}

package at.forsyte.apalache.tla.lir.oper

/**
 * The operators defined in the TLC module. Many user modules import TLC, so it is a good idea to have a stub for TLC.
 *
 * @author konnov
 */
abstract class TlcOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object TlcOper {

  /**
   * Operator `Print(out, val)` from TLC.
   */
  object print extends TlcOper {
    override def name: String = "TLC!Print"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `PrintT(out)` from TLC.
   */
  object printT extends TlcOper {
    override def name: String = "TLC!PrintT"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `Assert(out, val)` from TLC.
   */
  object assert extends TlcOper {
    override def name: String = "TLC!Assert"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `JavaTime` from TLC.
   */
  object javaTime extends TlcOper {
    override def name: String = "TLC!javaTime"
    override def arity: OperArity = FixedArity(0)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `TLCGet(i)` from TLC.
   */
  object tlcGet extends TlcOper {
    override def name: String = "TLC!TLCGet"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `TLCSet(i, v)` from TLC.
   */
  object tlcSet extends TlcOper {
    override def name: String = "TLC!TLCSet"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Singleton function in TLC: `a :> b`.
   */
  object colonGreater extends TlcOper {
    override def name: String = "TLC!:>"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (7, 7)
  }

  /**
   * Function concatenation in TLC: `f @@ g`.
   */
  object atat extends TlcOper {
    override def name: String = "TLC!@@"
    override def arity: OperArity = AnyArity()
    override val precedence: (Int, Int) = (6, 6)
  }

  /**
   * Operator `Permutations(S)` from TLC.
   */
  object permutations extends TlcOper {
    override def name: String = "TLC!Permutations"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `SortSeq(s, Op(_, _))` from TLC.
   */
  object sortSeq extends TlcOper {
    override def name: String = "TLC!SortSeq"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `RandomElement(S)` from TLC.
   */
  object randomElement extends TlcOper {
    override def name: String = "TLC!RandomElement"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `Any` from TLC.
   */
  object any extends TlcOper {
    override def name: String = "TLC!Any"
    override def arity: OperArity = FixedArity(0)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `ToString(S)` from TLC.
   */
  object tlcToString extends TlcOper {
    override def name: String = "TLC!ToString"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * Operator `TLCEval(v)` from TLC.
   */
  object tlcEval extends TlcOper {
    override def name: String = "TLC!TLCEval"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (16, 16)
  }
}

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
    * Print(out, val) from TLC.
    */
  val print: TlcOper = new TlcOper {
    override def name: String = "TLC!Print"
    override def arity: OperArity = FixedArity(2)
  }

  /**
    * PrintT(out) from TLC.
    */
  val printT: TlcOper = new TlcOper {
    override def name: String = "TLC!PrintT"
    override def arity: OperArity = FixedArity(1)
  }

  /**
    * Assert(out, val) from TLC.
    */
  val assert: TlcOper = new TlcOper {
    override def name: String = "TLC!Assert"
    override def arity: OperArity = FixedArity(2)
  }

  /**
    * JavaTime from TLC.
    */
  val javaTime: TlcOper = new TlcOper {
    override def name: String = "TLC!javaTime"
    override def arity: OperArity = FixedArity(0)
  }

  /**
    * TLCGet(i) from TLC.
    */
  val tlcGet: TlcOper = new TlcOper {
    override def name: String = "TLC!TLCGet"
    override def arity: OperArity = FixedArity(1)
  }

  /**
    * TLCSet(i, v) from TLC.
    */
  val tlcSet: TlcOper = new TlcOper {
    override def name: String = "TLC!TLCSet"
    override def arity: OperArity = FixedArity(2)
  }

  /**
    * _ :> _ from TLC.
    */
  val colonGreater: TlcOper = new TlcOper {
    override def name: String = "TLC!:>"
    override def arity: OperArity = FixedArity(2)
  }

  /**
    * _ @@ _ from TLC.
    */
  val atat: TlcOper = new TlcOper {
    override def name: String = "TLC!@@"
    override def arity: OperArity = FixedArity(2)
  }

  /**
    * Permutations(S) from TLC.
    */
  val permutations: TlcOper = new TlcOper {
    override def name: String = "TLC!Permutations"
    override def arity: OperArity = FixedArity(1)
  }

  /**
    * SortSeq(s, Op(_, _)) from TLC.
    */
  val sortSeq: TlcOper = new TlcOper {
    override def name: String = "TLC!SortSeq"
    override def arity: OperArity = FixedArity(2)
  }

  /**
    * RandomElement(S) from TLC.
    */
  val randomElement: TlcOper = new TlcOper {
    override def name: String = "TLC!RandomElement"
    override def arity: OperArity = FixedArity(1)
  }

  /**
    * any from TLC.
    */
  val any: TlcOper = new TlcOper {
    override def name: String = "TLC!Any"
    override def arity: OperArity = FixedArity(0)
  }

  /**
    * ToString(S) from TLC.
    */
  val tlcToString: TlcOper = new TlcOper {
    override def name: String = "TLC!ToString"
    override def arity: OperArity = FixedArity(1)
  }

  /**
    * TLCEval(v) from TLC.
    */
  val tlcEval: TlcOper = new TlcOper {
    override def name: String = "TLC!TLCEval"
    override def arity: OperArity = FixedArity(1)
  }
}



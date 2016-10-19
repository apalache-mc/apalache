package at.forsyte.apalache.tla

package lir {
  import at.forsyte.apalache.tla.lir.oper.TlaOper


  /** the base class for all TLA+ objects */
  abstract class TlaValue

/** a constant as defined by CONSTANT */
  class TlaConst(val name: String) extends TlaValue

  /** a variable as defined by VARIABLE */
  class TlaVar(val name: String) extends TlaValue

  /** A scope in which constants and variables are declared */
  trait TlaScope {
    def declareConst(name: String): TlaConst
    def declareVar(name: String): TlaVar
    def lookup(name: String): TlaValue
  }

  /** A TLA+ expression */
  abstract class TlaEx
  case class ValEx(value: TlaValue) extends TlaEx

  case class OperEx(oper: TlaOper, args: TlaEx*) extends TlaEx {
    require(oper.isCorrectArity(args.size), "unexpected arity %d".format(args.size))
  }
}

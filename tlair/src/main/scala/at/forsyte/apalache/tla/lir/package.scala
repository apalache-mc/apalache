package at.forsyte.apalache.tla

package lir {
  import at.forsyte.apalache.tla.lir.oper._

  /** the base class for the universe of objects used in TLA+ */
  abstract class TlaValue

  /** a constant as defined by CONSTANT */
  class TlaConst(val name: String) extends TlaValue

  /** a variable as defined by VARIABLE */
  class TlaVar(val name: String) extends TlaValue

  /** A scope in which constants and variables are declared.
    * TODO: use the scope!
    */
  trait TlaScope {
    def declareConst(name: String): TlaConst
    def declareVar(name: String): TlaVar
    def lookup(name: String): TlaValue
  }

  /**
  A formal parameter of an operator. Note that one can use a formal parameter in a TLA+ expression,
        and thus FormalParam inherits from TlaValue.
    */
  abstract class Param {
    def name: String
    def arity: Int
  }

  /** An ordinary expression, e.g., x */
  case class SimpleParam(name: String) extends Param {
    override def arity = 0
  }

  /** A function signature, e.g., f(_, _) */
  case class OperParam(oper: TlaOper) extends Param {
    require(oper.arity match { case FixedArity(_) => true; case _ => false }, "Formal parameters should have fixed arity")

    override def name = oper.name

    override def arity =
      oper.arity match {
        case FixedArity(n) => n
        case _ => throw new IllegalStateException("Non-fixed arity") // it should not happen together with 'require'
      }

  }

  /** A TLA+ expression */
  abstract class TlaEx

  /** just using a TLA+ value */
  case class ValEx(value: TlaValue) extends TlaEx

  /** applying an operator, including the one defined by OperFormalParam */
  case class OperEx(oper: TlaOper, args: TlaEx*) extends TlaEx {
    require(oper.isCorrectArity(args.size), "unexpected arity %d".format(args.size))
  }

  /**
    Using a formal parameter, which is not an OperFormalParam.

    TODO: we don't like it, find a better solution. The problem is that one has to write SimpleParamEx(SimpleParam("x"))
      to refer to a formal parameter.
    */
  case class SimpleParamEx(param: SimpleParam)


  /** An operator definition, e.g. A == 1 + 2, or B(x, y) == x + y, or (C(f(_, _), x, y) == f(x, y) */
  class TlaOperDef(val name: String, val formalParams: List[Param], val body: TlaEx) {
    val operName = name
    def createOperator(): TlaOper = {
      // TODO: maybe we should define a user-instantiated operator instead of an anonymous class
      new TlaOper {
        override def arity: OperArity = FixedArity(formalParams.length)
        override def interpretation: Interpretation.Value = Interpretation.User
        override def name: String = operName
      }
    }
  }

}

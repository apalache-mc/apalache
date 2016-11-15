package at.forsyte.apalache.tla

package lir {
  
  import at.forsyte.apalache.tla.lir.oper._
  
  /** the base class for the universe of objects used in TLA+ */
  abstract class TlaValue
  
  /** a declaration, e.g., of a variable, constant, or an operator */
  abstract class TlaDecl {
    def name: String
  }
  
  /** a constant as defined by CONSTANT */
  class TlaConstDecl(val name: String) extends TlaDecl
  
  /** a variable as defined by VARIABLE */
  class TlaVarDecl(val name: String) extends TlaDecl
  
  
  /**
  A formal parameter of an operator.
    */
  abstract class FormalParam {
    def name: String
  
    def arity: OperArity
  }
  
  /** An ordinary formal parameter, e.g., x used in A(x) == ... */
  case class SimpleFormalParam(name: String) extends FormalParam {
    override def arity: OperArity = FixedArity(0)
  }
  
  /** A function signature, e.g., f(_, _) used in A(f(_, _), x, y) */
  case class OperFormalParam(name: String, arity: OperArity) extends FormalParam {
    require(
      arity match {
        case FixedArity(_) => true;
        case _ => false
      },
      "Formal parameters should have fixed arity")
  }
  
  /** An abstract TLA+ expression */
  abstract class TlaEx
  
  /** just using a TLA+ value */
  case class ValEx(value: TlaValue) extends TlaEx
  
  /** refering to a variable, constant, operator, etc. by a name. */
  case class NameEx(name: String) extends TlaEx
  
  /** applying an operator, including the one defined by OperFormalParam */
  case class OperEx(oper: TlaOper, args: TlaEx*) extends TlaEx {
    require(oper.isCorrectArity(args.size), "unexpected arity %d".format(args.size))
  }
  
  
  /** An operator definition, e.g. A == 1 + 2, or B(x, y) == x + y, or (C(f(_, _), x, y) == f(x, y) */
  class TlaOperDecl(val name: String, val formalParams: List[FormalParam], val body: TlaEx)
      extends TlaDecl {

    def createOperator(): TlaOper = {
      // TODO: maybe we should define a user-instantiated operator instead of an anonymous class
      new TlaOper {
        override def arity: OperArity = FixedArity(formalParams.length)
  
        override def interpretation: Interpretation.Value = Interpretation.User
  
        override def name: String = TlaOperDecl.this.name
      }
    }
  }

/**
 * A module declaration.
 *
 * @param name the module name
 * @param imports the names of imported modules
 * @param declarations all kinds of declarations
 */
  class TlaModule(val name: String, val imports: Seq[String], declarations: Seq[TlaDecl])

}

package at.forsyte.apalache.tla

package lir {

  import at.forsyte.apalache.tla.lir.io.UTFPrinter
  import at.forsyte.apalache.tla.lir.oper._

  /** the base class for the universe of objects used in TLA+ */
  abstract class TlaValue

  /** a declaration, e.g., of a variable, constant, or an operator */
  abstract class TlaDecl {
    def name: String
    def deepCopy(): TlaDecl
  }

  // TODO: add TlaTheoremDecl?

  /**
    * A module as a basic unit that contains declarations.
    *
    * @param name the module name
    * @param imports the names of imported modules
    * @param declarations all kinds of declarations
    */
  class TlaModule(val name: String, val imports: Seq[String], val declarations: Seq[TlaDecl]) {
    def constDeclarations: Seq[TlaConstDecl] = {
      declarations.collect { case d: TlaConstDecl => d }
    }

    def varDeclarations: Seq[TlaVarDecl] = {
      declarations.collect { case d: TlaVarDecl => d }
    }

    def operDeclarations: Seq[TlaOperDecl] = {
      declarations.collect { case d: TlaOperDecl => d}
    }

    def assumeDeclarations: Seq[TlaAssumeDecl] = {
      declarations.collect { case d: TlaAssumeDecl => d}
    }
  }

  /** a constant as defined by CONSTANT */
  case class TlaConstDecl(name: String) extends TlaDecl{
    override def deepCopy( ): TlaConstDecl =  TlaConstDecl( name )
  }

  /** a variable as defined by VARIABLE */
  case class TlaVarDecl(name: String) extends TlaDecl{
    override def deepCopy( ): TlaVarDecl =  TlaVarDecl( name )
  }

  /**
    * An assumption defined by ASSUME(...)
    * @param body the assumption body
    */
  case class TlaAssumeDecl(body: TlaEx) extends TlaDecl {
    val name: String = "ASSUME"
    override def deepCopy(): TlaAssumeDecl = TlaAssumeDecl(body.deepCopy())
  }

  ///////////////// DISCUSSION

  /**
    * A spec, given by a list of declarations and a list of expressions.
    *
    * FIXME: a candidate for removal. Just use TlaModule?
    */
  case class TlaSpec( name: String, declarations: List[TlaDecl] ){
    def deepCopy() : TlaSpec = TlaSpec( name, declarations.map( _.deepCopy() ) )

  }

  ///////////////// END of DISCUSSION


  /**
  A formal parameter of an operator.
    */
  sealed abstract class FormalParam {
    def name: String

    def arity: OperArity   /** Simplify arity to Int, Jure 16.11.2017 */

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

  /** An abstract TLA+ expression. Note that the class is sealed, so we allow only a limited set of values. */
  sealed abstract class TlaEx extends Identifiable {

    // TODO: there must be a nice way of defining default printers in scala, so we do not have to make a choice here
    override def toString: String =  UTFPrinter( this )

    def toSimpleString: String = ""

    def deepCopy() : TlaEx
  }

  /**
    * This is a special expression that indicates that this expression does not have a meaningful value.
    * For instance, this expression can be used as the body of a library operator, which by default have
    * gibberish definitions by SANY.
    * We could use Option[TlaEx], but that would introduce unnecessary many pattern matches, as NoneEx will be rare.
    */
  object NullEx extends TlaEx {
    override def deepCopy() : TlaEx = NullEx
    override def toSimpleString: String = toString
  }

  /** just using a TLA+ value */
  case class ValEx(value: TlaValue) extends TlaEx{
    override def toSimpleString: String = value.toString
    override def deepCopy() : ValEx = ValEx( value )
  }

  /** referring to a variable, constant, operator, etc. by a name. */
  case class NameEx(name: String) extends TlaEx{
    override def toSimpleString: String = name
    override def deepCopy() : NameEx = NameEx(name)
  }

  // applying an operator, including the one defined by OperFormalParam

  /**
    * NOTE: Scala does not auto-generate copy for OperEx, because args are variable
    * IK: Let's discuss it. To my understanding, case classes copy their parameters without any problem.
    */

  case class OperEx(oper: TlaOper, args: TlaEx*) extends TlaEx {
    require(oper.isCorrectArity(args.size),
      "unexpected arity %d in %s applied to %s".format(args.size, oper.name, args.map(_.toString) mkString ", "))

    require(oper.permitsArgs(args),
      "The invariant of %s is violated by the arguments: %s".format(oper.name, args.map(_.toString) mkString ", "))

    override def toSimpleString: String = {
      oper.arity match{
        case FixedArity(n) => {
          n match {
            case 1 => args.head.toSimpleString + oper.name
            case 2 => args.head.toSimpleString + " " + oper.name + " " + args.tail.head.toSimpleString
            case _ => oper.name +"(" + args.map( _.toSimpleString ).mkString(", ") + ")"
          }
        }
        case _ => oper.name +"(" + args.map( _.toSimpleString ).mkString(", ") + ")"

      }
    }

    override def deepCopy() : OperEx =  OperEx( oper, args.map( _.deepCopy() ) : _* )
  }

  /**
    * A user-defined operator that is created from an operator declaration.
    * Normally, user-defined operators are created from the operator declarations.
    *
    * @see TlaOperDecl
    *
    * @param name operator name
    * @param arity operator arity
    * @param decl the declaration, from which the operator was instantiated
    */
  class TlaUserOper(val name: String, val arity: OperArity, val decl: TlaOperDecl) extends TlaOper {
    override def interpretation = Interpretation.User

    // as this is not a case class, we have to carefully define equality and hashCode
    override def equals(that: scala.Any): Boolean = {
      that match {
        case that: TlaUserOper =>
          that.name == name && that.arity == arity && that.decl == decl

        case _ =>
          false
      }
    }

    override def hashCode(): Int = {
      31 * (31 * name.hashCode + arity.hashCode()) + decl.hashCode()
    }
  }


  /**
    * <p>An operator definition, e.g. A == 1 + 2, or B(x, y) == x + y, or (C(f(_, _), x, y) == f(x, y).</p>
    *
    * <p>As in the case with the built-in operators, every operator declaration carries a single operator instance,
    * which is stored in the public field 'operator'. However, if the operator is recursive, then the operator body
    * does not contain OperEx(this.operator, ...), but it does contain OperFormalOperParam(this.name),
    * see TlaRecOperDecl.</p>
    *
    * <p>Note that the body is declared as a variable, which can be overwritten later. We need it to deal with INSTANCE.
    * Similarly, isRecursive is false by default, but it can be set to true during instantiation.
    * </p>
    *
    * @see TlaRecOperDecl
    *
    * @param name operator name
    * @param formalParams formal parameters
    * @param body operator definition, that is a TLA+ expression that captures the operator definition
    */
  case class TlaOperDecl( name: String, formalParams: List[FormalParam], var body: TlaEx ) extends TlaDecl {
    // this is no longer required, as module instantiation uses null bodies
    //    require( !body.isNull )

    val operator: TlaUserOper = new TlaUserOper(name, FixedArity(formalParams.length), this)
    /**
      * Is the operator definition recursive? Similar to body, this is a variable that can be changed later.
      */
    var isRecursive: Boolean = false

    override def deepCopy( ): TlaOperDecl =  TlaOperDecl( name, formalParams, body.deepCopy() )
  }

}



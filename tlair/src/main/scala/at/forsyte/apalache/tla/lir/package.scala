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
    // why do we need it here?
    def identical( other: TlaDecl ) : Boolean
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
    override def identical( other: TlaDecl ): Boolean = this == other
  }

  /** a variable as defined by VARIABLE */
  case class TlaVarDecl(name: String) extends TlaDecl{
    override def deepCopy( ): TlaVarDecl =  TlaVarDecl( name )
    override def identical( other: TlaDecl ): Boolean = this == other

  }

  /**
    * An assumption defined by ASSUME(...)
    * @param body the assumption body
    */
  case class TlaAssumeDecl(body: TlaEx) extends TlaDecl {
    val name: String = "ASSUME"
    override def deepCopy(): TlaAssumeDecl = TlaAssumeDecl(body.deepCopy(identified = false))
    override def identical(other: TlaDecl): Boolean = this == other
  }

  ///////////////// DISCUSSION
  /**
    * A module included by EXTENDS.
    *
    * FIXME: shall we remove this one, as there is no obvious for it? Just use TlaModule.
    */
  case class TlaModuleDecl(name: String) extends TlaDecl{
    override def deepCopy( ): TlaModuleDecl =  TlaModuleDecl( name )
    override def identical( other: TlaDecl ): Boolean = this == other
  }

  /**
    * A spec, given by a list of declarations and a list of expressions.
    *
    * FIXME: a candidate for removal. Just use TlaModule?
    */
  case class TlaSpec( name: String, declarations: List[TlaDecl] ){
    def deepCopy() : TlaSpec = {
      return TlaSpec( name, declarations.map( _.deepCopy() ) )
    }
    def identical( other: TlaSpec ): Boolean =
      ( name == other.name
        && declarations.zip( other.declarations ).forall( pa => pa._1.identical( pa._2 ) )
        )
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
    // TODO: hey, use power of Scala! Move toNiceString out of here and introduce a PrettyPrinter class.
    // No need, toString suffices, you can just call print( ex ) which invokes it by default.
    def toNiceString( nTab: Int = 0) = ""

    // TODO: there must be a nice way of defining default printers in scala, so we do not have to make a choice here
    override def toString: String =  UTFPrinter( this )

    def toSimpleString: String = ""

    // TODO: goes to PrettyPrinter
    protected val indent : Int = 4
    // TODO: goes to PrettyPrinter
    protected val tab : String = " " * indent

    def isNull : Boolean = false

    def deepCopy( identified: Boolean = true ) : TlaEx

    // this is a strange method, as it expects both structural equality and equality of the identifiers
    def identical( other: TlaEx ) : Boolean
  }

  /**
    * This is a special expression that indicates that this expression does not have a meaningful value.
    * For instance, this expression can be used as the body of a library operator, which by default have
    * gibberish definitions by SANY.
    * We could use Option[TlaEx], but that would introduce unnecessary many pattern matches, as NoneEx will be rare.
    */
  object NullEx extends TlaEx {
    override def deepCopy(identified: Boolean): TlaEx = NullEx
    override def identical(other: TlaEx): Boolean = this eq other

    override def toNiceString(nTab: Int): String = "NullEx"
    override def toSimpleString: String = toNiceString()
    override def isNull : Boolean = true
  }

  /** just using a TLA+ value */
  case class ValEx(value: TlaValue) extends TlaEx{
    override def toNiceString( nTab : Int = 0): String = (tab *nTab) + "( ValEx: " + value.toString + " , id:" + ID + " )"
    override def toSimpleString: String = value.toString
    override def deepCopy( identified: Boolean = true ): ValEx = {
      val ret = ValEx( value )
      if (identified) {
        ret.m_ID = m_ID
        ret.canSet = canSet
      }
      return ret
    }

    // TODO: move it an analysis class. This can be done by pattern matching and should not be in the class itself.
    override def identical( other: TlaEx ): Boolean = {
      other match{
        case ValEx( v ) => v == value && other.ID == ID
        case _ => false
      }
    }

  }

  /** referring to a variable, constant, operator, etc. by a name. */
  case class NameEx(name: String) extends TlaEx{
    override def toNiceString( nTab: Int = 0 ): String = (tab *nTab) + "( NameEx: " + name + " , id: " + ID + " )"
    override def toSimpleString: String = name
    override def deepCopy(identified: Boolean = true): NameEx = {
      val ex = NameEx(name)
      if (identified) {
        ex.m_ID = m_ID
        ex.canSet = canSet
      }
      ex
    }

    // TODO: move it an analysis class. This can be done by pattern matching and should not be in the class itself.
    override def identical( other: TlaEx ): Boolean = {
      other match{
        case NameEx( nm ) => nm == name && other.ID == ID
        case _ => false
      }
    }
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

    override def toNiceString( nTab : Int = 0 ): String = {
      (tab *nTab) + "( OperEx: " +
        oper.name + ",\n" +
        args.map( (x : TlaEx) => x.toNiceString( nTab + 1 )).mkString(",\n") +
        ",\n" + (tab *nTab) + "  id: " + ID + "\n"+ (tab *nTab) + ")"
    }

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

    // TODO: remove it, copying should work automatically for case classes
    override def deepCopy( identified: Boolean = true ): OperEx = {
      val ex = OperEx( oper, args.map( _.deepCopy( identified ) ) : _* ) // deep copy
      if (identified) {
        ex.m_ID = m_ID
        ex.canSet = canSet
      }
      ex
    }

    // TODO: move it an analysis class. This can be done by pattern matching and should not be in the class itself.
    override def identical( other: TlaEx ): Boolean = {
      other match{
        case OperEx( op, arguments @ _*  ) => op == oper && other.ID == ID && arguments.size == args.size &&
          args.zip(arguments).forall( pa => pa._1.identical( pa._2 ) )
        case _ => false
      }
    }

    // TODO: what is that and why do we need it?
    def deepForget( ): Unit = {
      forget()
      args.foreach( _.forget() )
    }

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

    // TODO: remove
    override def identical( other: TlaDecl ): Boolean = other match {
      case TlaOperDecl( oname, oparams, obody ) => name == oname && formalParams == oparams && body.identical( obody )
      case _ => false
    }
  }

}



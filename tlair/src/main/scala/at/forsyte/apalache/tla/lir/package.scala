package at.forsyte.apalache.tla

package lir {
  
  import at.forsyte.apalache.tla.lir.oper._

  /** the base class for the universe of objects used in TLA+ */
  abstract class TlaValue
  
  /** a declaration, e.g., of a variable, constant, or an operator */
  abstract class TlaDecl {
    def name: String
    def deepCopy(): TlaDecl
    def identical( other: TlaDecl ) : Boolean
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

  /** a module included by EXTENDS */
  case class TlaModuleDecl(name: String) extends TlaDecl{
    override def deepCopy( ): TlaModuleDecl =  TlaModuleDecl( name )
    override def identical( other: TlaDecl ): Boolean = this == other
  }

  /** a spec, given by a list of declarations and a list of expressions */
  case class TlaSpec( name: String, declarations: List[TlaDecl] ){
    def deepCopy() : TlaSpec = {
      return TlaSpec( name, declarations.map( _.deepCopy() ) )
    }
    def identical( other: TlaSpec ): Boolean =
      ( name == other.name
        && declarations.zip( other.declarations ).forall( pa => pa._1.identical( pa._2 ) )
        )
  }


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


  trait Identifiable{
    protected var m_ID : UID = UID( -1 )
    protected var canSet: Boolean = true
    def setID( newID: UID ) = {
      if( canSet ) {
        canSet = false
        m_ID = newID
      }
      else throw new Identifiable.IDReallocationError
    }
    def ID : UID = m_ID

    def forget(): Unit ={
      m_ID = UID( -1 )
      canSet = true
    }

  }

  object Identifiable extends Identifiable{
    class IDReallocationError extends Exception
  }

  /** An abstract TLA+ expression */
  abstract class TlaEx extends  Identifiable{

    // TODO: hey, use power of Scala! Move toNiceString out of here and introduce a PrettyPrinter class.
    def toNiceString( nTab: Int = 0) = ""
    override def toString: String = toNiceString()

    // TODO: goes to PrettyPrinter
    protected val indent : Int = 4
    // TODO: goes to PrettyPrinter
    protected val tab : String = " " *indent

    def deepCopy( identified: Boolean = true ) : TlaEx
    def identical( other: TlaEx ) : Boolean

  }

  /** just using a TLA+ value */
  case class ValEx(value: TlaValue) extends TlaEx{
    override def toNiceString( nTab : Int = 0): String = (tab *nTab) + "( ValEx: " + value.toString + " , id:" + ID + " )"

    override def deepCopy( identified: Boolean = true ): ValEx = {
      val ret = ValEx( value )
      if (identified) {
        ret.m_ID = m_ID
        ret.canSet = canSet
      }
      return ret
    }

    override def identical( other: TlaEx ): Boolean = {
      other match{
        case ValEx( v ) => v == value && other.ID == ID
        case _ => false
      }
    }

  }

  /** refering to a variable, constant, operator, etc. by a name. */
  case class NameEx(name: String) extends TlaEx{
    override def toNiceString( nTab: Int = 0 ): String = (tab *nTab) + "( NameEx: " + name + " , id: " + ID + " )"
    override def deepCopy( identified: Boolean = true ): NameEx = {
      val ret = NameEx( name )
      if (identified) {
        ret.m_ID = m_ID
        ret.canSet = canSet
      }
      return ret
    }

    override def identical( other: TlaEx ): Boolean = {
      other match{
        case NameEx( nm ) => nm == name && other.ID == ID
        case _ => false
      }
    }
  }

  /** applying an operator, including the one defined by OperFormalParam */

  /** NOTE: Scala does not auto-generate copy for OperEx, because args are variable */

  case class OperEx(oper: TlaOper, args: TlaEx*) extends TlaEx {
    require(oper.isCorrectArity(args.size), "unexpected arity %d".format(args.size))
    override def toNiceString( nTab : Int = 0 ): String = {
      (tab *nTab) + "( OperEx: " +
        oper.name + ",\n" +
        args.map( (x : TlaEx) => x.toNiceString( nTab + 1 )).mkString(",\n") +
        ",\n" + (tab *nTab) + "  id: " + ID + "\n"+ (tab *nTab) + ")"
    }

    override def deepCopy( identified: Boolean = true ): OperEx = {
      val ret = new OperEx( oper, args.map( _.deepCopy( identified ) ) : _* ) // deep copy
      if (identified) {
        ret.m_ID = m_ID
        ret.canSet = canSet
      }
      return ret
    }

    override def identical( other: TlaEx ): Boolean = {
      other match{
        case OperEx( op, arguments @ _*  ) => op == oper && other.ID == ID && arguments.size == args.size &&
          args.zip(arguments).forall( pa => pa._1.identical( pa._2 ) )
        case _ => false
      }
    }

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
  }


  /**
    * An operator definition, e.g. A == 1 + 2, or B(x, y) == x + y, or (C(f(_, _), x, y) == f(x, y).
    * As in the case of built-in operators, every operator declaration carries a single operator instance,
    * which is stored in the public field 'operator'.
    */
  case class TlaOperDecl( name: String, formalParams: List[FormalParam], body: TlaEx )
      extends TlaDecl {

    val operator: TlaUserOper = new TlaUserOper(name, FixedArity(formalParams.length), this)

    override def deepCopy( ): TlaOperDecl =  TlaOperDecl( name, formalParams, body.deepCopy() )

    override def identical( other: TlaDecl ): Boolean = other match{
      case TlaOperDecl( oname, oparams, obody ) => name == oname && formalParams == oparams && body.identical( obody )
      case _ => false
    }
  }

/**
 * A module declaration.
 *
 * @param name the module name
 * @param imports the names of imported modules
 * @param declarations all kinds of declarations
 */
  class TlaModule(val name: String, val imports: Seq[String], val declarations: Seq[TlaDecl])


  abstract class IDType
  case class UID( id: Int ) extends IDType
  case class EID( id: Int ) extends IDType


}

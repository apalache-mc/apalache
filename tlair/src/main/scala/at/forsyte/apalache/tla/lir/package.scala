package at.forsyte.apalache.tla

package lir {

  import at.forsyte.apalache.tla.lir.io.UTFPrinter
  import at.forsyte.apalache.tla.lir.oper._

  /** the base class for the universe of values (integers, Booleans, strings) used in TLA+ */
  abstract class TlaValue

  /**
   * A declaration, e.g., of a variable, constant, or an operator.
   * Technically, this class should be called TlaDef, as we are dealing with
   * TLA+ definitions, see Specifying Systems, Ch. 17.3. Unfortunately, there are
   * variable declarations and operator definitions...
   */
  abstract class TlaDecl extends Identifiable with Serializable {
    def name: String
  }

  /**
   * A module as a basic unit that contains declarations.
   *
   * @param name         the module name
   * @param declarations all kinds of declarations
   */
  class TlaModule(val name: String, val declarations: Seq[TlaDecl]) extends Serializable {
    def constDeclarations: Seq[TlaConstDecl] = {
      declarations.collect { case d: TlaConstDecl => d }
    }

    def varDeclarations: Seq[TlaVarDecl] = {
      declarations.collect { case d: TlaVarDecl => d }
    }

    def operDeclarations: Seq[TlaOperDecl] = {
      declarations.collect { case d: TlaOperDecl => d }
    }

    def assumeDeclarations: Seq[TlaAssumeDecl] = {
      declarations.collect { case d: TlaAssumeDecl => d }
    }

    def canEqual(other: Any): Boolean = other.isInstanceOf[TlaModule]

    override def equals(other: Any): Boolean = other match {
      case that: TlaModule =>
        (that canEqual this) &&
          name == that.name &&
          declarations == that.declarations
      case _ => false
    }

    override def hashCode(): Int = {
      val state = Seq(name, declarations)
      state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
    }

    override def toString: String = {
      "TlaModule(%s) {\n%s\n}".format(name, declarations.mkString("\n"))
    }
  }

  /** a constant as defined by CONSTANT */
  case class TlaConstDecl(name: String) extends TlaDecl with Serializable

  /** a variable as defined by VARIABLE */
  case class TlaVarDecl(name: String) extends TlaDecl with Serializable

  /**
   * An assumption defined by ASSUME(...)
   *
   * @param body the assumption body
   */
  case class TlaAssumeDecl(body: TlaEx) extends TlaDecl with Serializable {
    val name: String = "ASSUME" + body.ID
  }

  /**
   * A spec, given by a list of declarations and a list of expressions.
   */
  case class TlaSpec(name: String, declarations: List[TlaDecl]) extends Serializable

  /**
   * A formal parameter of an operator.
   */
  sealed abstract class FormalParam extends Serializable {
    def name: String

    def arity: Int

  }

  /** An ordinary formal parameter, e.g., x used in A(x) == ... */
  case class SimpleFormalParam(name: String) extends FormalParam with Serializable {
    override def arity: Int = 0
  }

  /** A function signature, e.g., f(_, _) used in A(f(_, _), x, y) */
  case class OperFormalParam(name: String, arity: Int) extends FormalParam with Serializable {}

  /**
   * A type tag to be attached to a TLA+ language construct: an expression or a declaration.
   */
  sealed abstract class TypeTag

  /**
   * The type tag that simply indicates that the language construct is not typed.
   */
  case class Untyped() extends TypeTag

  /**
   * A type tag that carries a tag of type T, which the tag is parameterized with.
   *
   * @param myType the type that is carried by the tag
   * @tparam T the type of the tag
   */
  case class Typed[T](myType: T) extends TypeTag

  /**
   * Default settings for the untyped language layer. To use the `Untyped()` tag, import the definitions from `UntypedPredefs`.
   */
  object UntypedPredefs {
    implicit val untyped: TypeTag = Untyped()
  }

  /**
   * An abstract TLA+ expression. Note that the class is sealed, so we allow only a limited set of values.
   * Importantly, `TlaEx` accepts an implicit type tag.
   */
  sealed abstract class TlaEx(implicit val typeTag: TypeTag) extends Identifiable with Serializable {

    // TODO: there must be a nice way of defining default printers in scala, so we do not have to make a choice here.
    override def toString: String = UTFPrinter(this)

    def toSimpleString: String = ""
  }

  /**
   * This is a special expression that indicates that this expression does not have a meaningful value.
   * For instance, this expression can be used as the body of a library operator, which by default have
   * gibberish definitions by SANY.
   * We could use Option[TlaEx], but that would introduce unnecessary many pattern matches, as NoneEx is rare.
   * NullEx is always untyped.
   */
  object NullEx extends TlaEx()(typeTag = Untyped()) with Serializable {
    override def toSimpleString: String = toString
  }

  /**
   * A constant TLA+ value, which is usually a literal such as: 42, TRUE, "foo", BOOLEAN.
   * Importantly, `ValEx` accepts an implicit type tag.
   */
  case class ValEx(value: TlaValue)(implicit typeTag: TypeTag) extends TlaEx with Serializable {
    override def toSimpleString: String = value.toString
  }

  /**
   * Referring by name to a variable, constant, operator, etc.
   * Importantly, `NameEx` accepts an implicit type tag.
   */
  case class NameEx(name: String)(implicit typeTag: TypeTag) extends TlaEx with Serializable {
    override def toSimpleString: String = name
  }

  /*
   * A let-in definition, which is part of TLA+ syntax.
   * Importantly, `LetInEx` accepts an implicit type tag.
   */
  case class LetInEx(body: TlaEx, decls: TlaOperDecl*)(implicit typeTag: TypeTag) extends TlaEx with Serializable {
    override def toSimpleString: String = s"LET ${decls.mkString(" ")} IN $body"
  }

  /**
   * Application of a built-in operator. The standard operator `TlaOper.apply` allows us
   * to apply a user-defined operator (defined with `TlaOperDecl`) or an operator that is passed via a parameter
   * (that is, `OperFormalParam`). Importantly, `OperEx` accepts an implicit type tag.
   */
  case class OperEx(oper: TlaOper, args: TlaEx*)(implicit typeTag: TypeTag) extends TlaEx with Serializable {
    require(oper.isCorrectArity(args.size),
        "unexpected arity %d in %s applied to %s".format(args.size, oper.name, args.map(_.toString) mkString ", "))

    require(oper.permitsArgs(args),
        "The invariant of %s is violated by the arguments: %s".format(oper.name, args.map(_.toString) mkString ", "))

    override def toSimpleString: String = {
      oper.arity match {
        case FixedArity(n) => {
          n match {
            case 1 => args.head.toSimpleString + oper.name
            case 2 => args.head.toSimpleString + " " + oper.name + " " + args.tail.head.toSimpleString
            case _ => oper.name + "(" + args.map(_.toSimpleString).mkString(", ") + ")"
          }
        }
        case _ => oper.name + "(" + args.map(_.toSimpleString).mkString(", ") + ")"

      }
    }

  }

  /**
   * <p>An operator definition, e.g. A == 1 + 2, or B(x, y) == x + y, or (C(f(_, _), x, y) == f(x, y).</p>
   *
   * <p>If the operator is recursive, then the operator body contains OperEx(TlaOper.apply, NameEx(operName), ...).</p>
   *
   * <p>Note that the body is declared as a variable, which can be overwritten later. We need it to deal with INSTANCE.
   * Similarly, isRecursive is false by default, but it can be set to true during instantiation.
   * </p>
   *
   * @param name         operator name
   * @param formalParams formal parameters
   * @param body         operator definition, that is a TLA+ expression that captures the operator definition
   */
  case class TlaOperDecl(name: String, formalParams: List[FormalParam], var body: TlaEx)
      extends TlaDecl with Serializable {

    /**
     * Is the operator definition recursive? Similar to body, this is a variable that can be changed later.
     */
    var isRecursive: Boolean = false

    // Temporary solution, until #345 is resolved
    def copy(
        name: String = this.name, formalParams: List[FormalParam] = this.formalParams, body: TlaEx = this.body
    ): TlaOperDecl = {
      val ret = TlaOperDecl(name, formalParams, body)
      ret.isRecursive = this.isRecursive
      ret
    }

  }

  /**
   * <p>A definition of a recursive function, see [Specifying Systems][p. 67].</p>
   *
   * <p>For instance, Fact[n \in Nat] == IF n <= 1 THEN 1 ELSE n * Fact[n - 1].</p>
   *
   * @param name    the function name, e.g., Fact
   * @param arg     the name of the bound var, e.g., n
   * @param argDom  the expression that describes the variable bound, e.g., Nat
   * @param defBody the definition body
   */
  @deprecated("Use TlaFunOper.recFunDef and TlaFunOper.recFunRef instead")
  case class TlaRecFunDecl(name: String, arg: String, argDom: TlaEx, defBody: TlaEx) extends TlaDecl

  /**
   * <p>A THEOREM declaration. Currently, we do not support operators that are typically used in the proofs.</p>
   *
   * @param name theorem name
   * @param body theorem statement
   */
  case class TlaTheoremDecl(name: String, body: TlaEx) extends TlaDecl
}

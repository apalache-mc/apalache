package at.forsyte.apalache.tla.lir

/**
 * A declaration, e.g., of a variable, constant, or an operator.
 * Technically, this class should be called TlaDef, as we are dealing with
 * TLA+ definitions, see Specifying Systems, Ch. 17.3. Unfortunately, there are
 * variable declarations and operator definitions...
 */
abstract class TlaDecl(implicit val typeTag: TypeTag) extends Identifiable with Serializable with TypeTagged[TlaDecl] {
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
case class TlaConstDecl(name: String)(implicit typeTag: TypeTag) extends TlaDecl with Serializable {
  override def withType(newTypeTag: TypeTag): TlaConstDecl = TlaConstDecl(name)(newTypeTag)
}

/** a variable as defined by VARIABLE */
case class TlaVarDecl(name: String)(implicit typeTag: TypeTag) extends TlaDecl with Serializable {
  override def withType(newTypeTag: TypeTag): TlaVarDecl = TlaVarDecl(name)(newTypeTag)
}

/**
 * An assumption defined by ASSUME(...)
 *
 * @param body the assumption body
 */
case class TlaAssumeDecl(body: TlaEx)(implicit typeTag: TypeTag) extends TlaDecl with Serializable {
  val name: String = "ASSUME" + body.ID

  override def withType(newTypeTag: TypeTag): TlaAssumeDecl = TlaAssumeDecl(body)(newTypeTag)
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
case class TlaOperDecl(name: String, formalParams: List[FormalParam], var body: TlaEx)(implicit typeTag: TypeTag)
    extends TlaDecl with Serializable {

  /**
   * Is the operator definition recursive? Similar to body, this is a variable that can be changed later.
   */
  var isRecursive: Boolean = false

  // Temporary solution, until #345 is resolved
  def copy(
      name: String = this.name, formalParams: List[FormalParam] = this.formalParams, body: TlaEx = this.body
  ): TlaOperDecl = {
    val ret = TlaOperDecl(name, formalParams, body)(typeTag)
    ret.isRecursive = this.isRecursive
    ret
  }

  override def withType(newTypeTag: TypeTag): TlaOperDecl = TlaOperDecl(name, formalParams, body)(newTypeTag)
}

/**
 * <p>A THEOREM declaration. Currently, we do not support operators that are typically used in the proofs.</p>
 *
 * @param name theorem name
 * @param body theorem statement
 */
case class TlaTheoremDecl(name: String, body: TlaEx)(implicit typeTag: TypeTag) extends TlaDecl {
  override def withType(newTypeTag: TypeTag): TlaTheoremDecl = TlaTheoremDecl(name, body)(newTypeTag)
}

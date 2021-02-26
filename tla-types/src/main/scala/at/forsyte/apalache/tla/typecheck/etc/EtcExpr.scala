package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck.TlaType1

/**
 * An expression in a simple typed lambda calculus. Here we do not care about the concrete values,
 * but only care about the types that the expressions carry. Since we introduce type variables and quantifiers
 * in the principal types, this calculus is probably not that simple. If you have an idea, whether it is in
 * System F, or System F_\omega, or whatever, let us know.
 *
 * @author Igor Konnov
 */
sealed trait EtcExpr {

  /**
   * The reference to the source.
   * This identifier is not taken into account in equals and hash.
   */
  val sourceRef: EtcRef
}

/**
 * A constant expression, i.e., just a type (may be polymorphic).
 *
 * @param polytype a type constant that may have free variables (polytype).
 * @param sourceRef the identifier of the TLA+ expression that resulted in this EtcExpr (ignored in equals).
 */
case class EtcConst(polytype: TlaType1)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = {
    s"$sourceRef@$polytype"
  }
}

/**
 * A reference to a name, which can be introduced in the initial type context, or with EtcAbs.
 * Note that name is not a type variable, but rather a TLA+ name. The type can be retrieved
 * by looking up the name in the type context.
 *
 * @param name  a name
 * @param sourceRef the identifier of the TLA+ expression that resulted in this EtcExpr (ignored in equals).
 */
case class EtcName(name: String)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = s"$sourceRef@$name"
}

/**
 * Lambda abstraction that introduces an operator type
 * of multiple arguments that range over their respective types Set(*).
 *
 * @param body          the function body
 * @param paramsAndDoms parameter names and type expressions that encode sets of values
 * @param sourceRef     the identifier of the TLA+ expression that resulted in this EtcExpr (ignored in equals).
 */
case class EtcAbs(body: EtcExpr, paramsAndDoms: (EtcName, EtcExpr)*)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = {
    val bindings = paramsAndDoms.map(p => "%s ∈ %s".format(p._1, p._2))
    "%s@λ %s. %s".format(sourceRef, String.join(", ", bindings: _*), body)
  }
}

/**
 * Application of an operator whose signature is known. An operator may have several overloaded polytypes, e.g., f[e].
 *
 * @param operTypes  an Etc expression that represents an operator type
 * @param args  operator arguments
 * @param sourceRef the identifier of the TLA+ expression that resulted in this EtcExpr (ignored in equals).
 */
case class EtcApp(operTypes: Seq[TlaType1], args: EtcExpr*)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = {
    "%s@((%s) %s)".format(sourceRef, String.join(" | ", operTypes.map(_.toString): _*),
        String.join(" ", args.map(_.toString): _*))
  }
}

/**
 * Application of an operator by its name. The operator type should be resolved with a type signature that is
 * encoded in a type context.
 *
 * @param name operator name
 * @param args operator arguments
 * @param sourceRef identifier of the TLA+ expression that resulted in this EtcExpr (ignored in equals).
 */
case class EtcAppByName(name: String, args: EtcExpr*)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = {
    "%s@(%s %s)".format(sourceRef, name, String.join(" ", args.map(_.toString): _*))
  }
}

/**
 * Bind an expression to a name. To bind an operator of multiple arguments, use EtcAbs.
 * The operator type should be resolved with a type signature that is encoded in a type context.
 *
 * @param name  an expression name in the let-in binding
 * @param bound the expression to bind
 * @param body  the expression the binding applies to
 * @param sourceRef the identifier of the TLA+ expression that resulted in this EtcExpr (ignored in equals).
 */
case class EtcLet(name: String, bound: EtcExpr, body: EtcExpr)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = {
    "%s@let %s = %s in %s".format(sourceRef, name, bound, body)
  }
}

/**
 * A built-in type annotation for a name. In a programming language, like Scala, a type annotation is usually
 * given right in the declaration. In the TLA+ case, type declarations are not part of the language.
 * That is why we separate EtcTypeDecl from EtcLet. In a TLA+ specification, a type annotation may be placed
 * far away from the variable declaration.
 *
 * @param name a name, with which the type is associated
 * @param declaredType the type to be associated with the name
 * @param scopedEx the expression in the scope of the type declaration
 * @param sourceRef a reference to the original expression
 */
case class EtcTypeDecl(name: String, declaredType: TlaType1, scopedEx: EtcExpr)(val sourceRef: EtcRef) extends EtcExpr {
  override def toString: String = {
    "%s@%s: %s in %s".format(sourceRef, name, declaredType, scopedEx)
  }
}

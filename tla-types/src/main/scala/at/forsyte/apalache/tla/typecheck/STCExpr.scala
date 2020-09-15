package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.UID

/**
  * An expression in a simple typed lambda calculus. Here we do not care about the concrete values,
  * but only care about the types that the expressions carry. Since we introduce type variables and quantifiers
  * in the principal types, this calculus is probably not that simple. If you have an idea, whether it is in
  * System F, or System F_\omega, or whatever, let us know.
  *
  * @author Igor Konnov
  */
sealed trait STCExpr {
  /**
    * The identifier of the TLA+ expression that resulted in this STCExpr.
    * This identifier is not taken into account in equals and hash.
    */
  val tlaId: UID
}

/**
  * A constant expression, i.e., just a type (may be polymorphic).
  *
  * @param types a list type constants; usually, a singleton, but may be more, in case of overloaded operators.
  * @param tlaId the identifier of the TLA+ expression that resulted in this STCExpr (ignored in equals).
  */
case class STCConst(types: TlaType1*)(val tlaId: UID) extends STCExpr {
  override def toString: String = {
    tlaId + "@(" + String.join(" | ", types.map(_.toString): _*) + ")"
  }
}

/**
  * A reference to a name, which can be introduced in the initial type context, or with STCAbs.
  * Note that name is not a type variable, but rather a TLA+ name that carries a type.
  *
  * @param name  a name
  * @param tlaId the identifier of the TLA+ expression that resulted in this STCExpr (ignored in equals).
  */
case class STCName(name: String)(val tlaId: UID) extends STCExpr {
  override def toString: String = tlaId + "@" + name
}

/**
  * Lambda abstraction that introduces an operator type
  * of multiple arguments that range over their respective types Set(*).
  *
  * @param body          the function body
  * @param paramsAndDoms parameter names and type expressions that encode sets of values
  * @param tlaId         the identifier of the TLA+ expression that resulted in this STCExpr (ignored in equals).
  */
case class STCAbs(body: STCExpr, paramsAndDoms: (String, STCExpr)*)(val tlaId: UID) extends STCExpr {
  override def toString: String = {
    val bindings = paramsAndDoms.map(p => "%s ∈ %s".format(p._1, p._2))
    tlaId + "@λ %s. %s".format(String.join(", ", bindings: _*), body)
  }
}

/**
  * Operator application. We are talking about operators of the simple typed lambda calculus.
  *
  * @param oper  an STC expression that represents an operator type
  * @param args  function arguments
  * @param tlaId the identifier of the TLA+ expression that resulted in this STCExpr (ignored in equals).
  */
case class STCApp(oper: STCExpr, args: STCExpr*)(val tlaId: UID) extends STCExpr {
  override def toString: String = {
    tlaId + "@(%s %s)".format(oper, String.join(" ", args.map(_.toString): _*))
  }
}

/**
  * Bind an expression to a name. To bind an operator of multiple arguments, use STCAbs.
  *
  * @param name  an expression name in the let-in binding
  * @param bound the expression to bind
  * @param body  the expression the binding applies to
  * @param tlaId the identifier of the TLA+ expression that resulted in this STCExpr (ignored in equals).
  */
case class STCLet(name: String, bound: STCExpr, body: STCExpr)(val tlaId: UID) extends STCExpr {
  override def toString: String = {
    tlaId + "@let %s = %s in %s".format(name, bound, body)
  }
}

/**
  * Introduce a type variable in the scope of an expression.
  * @param name the variable name
  * @param scope the expression, to which the type variable appplies
  * @param tlaId the identifier of the TLA+ expression that resulted in this STCExpr (ignored in equals).
  */
case class STCIntroTypeVar(name: String, scope: STCExpr)(val tlaId: UID) extends STCExpr {
  override def toString: String = {
    tlaId + "@LAMBDA %s. %s".format(name, scope)
  }
}
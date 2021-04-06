package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.io.annotations.{Annotation, AnnotationStr, StandardAnnotations}
import at.forsyte.apalache.io.annotations.store.{AnnotationStore, findAnnotation}
import at.forsyte.apalache.tla.lir.{SparseTupT1, ValEx, _}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.parser.{DefaultType1Parser, Type1ParseError}
import com.typesafe.scalalogging.LazyLogging

/**
 * <p>ToEtcExpr takes a TLA+ expression and produces an EtcExpr.
 * The most interesting part of this translation is dealing with the built-in operators.
 * This translator is an extension of the ideas that appear in SignatureGenerator by Jure Kukovec.</p>
 *
 * @see at.forsyte.apalache.tla.types.SignatureGenerator
 * @author Igor Konnov
 */
class ToEtcExpr(annotationStore: AnnotationStore, aliasSubstitution: ConstSubstitution, varPool: TypeVarPool)
    extends EtcBuilder with LazyLogging {
  private val type1Parser = DefaultType1Parser

  def apply(decl: TlaDecl, inScopeEx: EtcExpr): EtcExpr = {
    decl match {
      case d: TlaConstDecl =>
        // CONSTANT N
        findTypeFromTagOrAnnotation(d).map(tt => mkTypeDecl(ExactRef(d.ID), d.name, tt, inScopeEx)).getOrElse(inScopeEx)

      case d: TlaVarDecl =>
        // VARIABLE x
        findTypeFromTagOrAnnotation(d).map(tt => mkTypeDecl(ExactRef(d.ID), d.name, tt, inScopeEx)).getOrElse(inScopeEx)

      case d: TlaAssumeDecl =>
        // ASSUME(...)
        // Translate assume to let in. The only purpose of this let-in definition is to get checked later.
        // To check that the body is returning a boolean value, we wrap the assumption with Bool => Bool.
        val operType = OperT1(Seq(BoolT1()), BoolT1())
        val application = mkUniqApp(Seq(operType), this(d.body))
        // We have to introduce a lambda abstraction, as the type checker is expecting this form.
        mkLet(BlameRef(d.ID), "__Assume_" + d.ID, mkAbs(ExactRef(d.ID), application), inScopeEx)

      case d: TlaOperDecl =>
        // Foo(x) == ...
        operDefToDecl(d, inScopeEx)

      case _ =>
        throw new TypingInputException(s"Unexpected declaration: $decl")
    }
  }

  /**
   * Translate an operator declaration.
   *
   * @param decl      an operator declaration
   * @param inScopeEx an expression to chain in the bottom of let-definition, it should have been translated
   * @return the translated let-in expression with inScopeEx attached
   */
  private def operDefToDecl(decl: TlaOperDecl, inScopeEx: EtcExpr): EtcExpr = {
    // The type of the lambda is what we want to see as the type of the declaration.
    // There are two cases: (1) the definition body contains a type annotation, and (2) no type annotation
    val paramsAndDoms = formalParamsToTypeVars(decl.formalParams).map { case (paramName, paramType) =>
      (mkName(BlameRef(decl.ID), paramName), mkConst(BlameRef(decl.ID), SetT1(paramType)))
    }

    def mkLetAbs(id: UID, expr: EtcExpr, paramsAndDoms: (EtcName, EtcConst)*) = {
      val lambda = mkAbs(ExactRef(id), expr, paramsAndDoms: _*)
      mkLet(BlameRef(id), decl.name, lambda, inScopeEx)
    }

    findTypeFromTagOrAnnotation(decl) match {
      case Some(tt) =>
        // case 1: the definition is either annotated with a java-like annotation in a comment, or tagged with TlaType1
        val fixedType = fixLazyAnnotation(decl, tt)
        val letAbs = mkLetAbs(decl.ID, this(decl.body), paramsAndDoms: _*)
        mkTypeDecl(ExactRef(decl.ID), decl.name, fixedType, letAbs)

      case None =>
        // case 2: no type annotation
        mkLetAbs(decl.ID, this(decl.body), paramsAndDoms: _*)
    }
  }

  // We let the user to write a instead of () => a for nullary operators. This method fixes such a lazy annotation.
  private def fixLazyAnnotation(decl: TlaOperDecl, tt: TlaType1): TlaType1 = {
    if (decl.formalParams.isEmpty && !tt.isInstanceOf[OperT1]) {
      OperT1(Seq(), tt)
    } else {
      tt
    }
  }

  // parse type from its text representation
  private def parseType(where: String, text: String): TlaType1 = {
    try {
      val (tt, _) = aliasSubstitution(type1Parser.parseType(text))
      renameVars(tt)
    } catch {
      case e: Type1ParseError =>
        logger.error("Parsing error in the type annotation: " + text)
        throw new TypingInputException(
            s"Parser error in type annotation of $where: ${e.msg}"
        )
    }
  }

  private def findTypeFromTagOrAnnotation(decl: TlaDecl): Option[TlaType1] = {
    decl.typeTag match {
      case Typed(tt: TlaType1) =>
        Some(tt)

      case _ =>
        // use a type annotation, if there is any
        findAnnotation(annotationStore, decl.ID, StandardAnnotations.TYPE) map {
          case Annotation(StandardAnnotations.TYPE, AnnotationStr(annotationText)) =>
            parseType(decl.name, annotationText)

          case a =>
            throw new TypingInputException(s"Unexpected annotation of ${decl.name}: $a")
        }
    }
  }

  private val typeOfLiteralExpr: TlaValue => TlaType1 = {
    case TlaInt(_)  => IntT1()
    case TlaBool(_) => BoolT1()
    case TlaStr(_)  => StrT1()
    case TlaReal()  => RealT1()
    case TlaIntSet  => SetT1(IntT1())
    case TlaNatSet  => SetT1(IntT1())
    case TlaRealSet => SetT1(RealT1())
    case TlaBoolSet => SetT1(BoolT1())
    case TlaStrSet  => SetT1(StrT1())
  }

  private def typeOfBoolOperArgs(args: Seq[TlaEx]): OperT1 = {
    val nBools = List.fill(args.length)(BoolT1())
    OperT1(nBools, BoolT1())
  }

  // Valid when the input seq has two items, the first of which is a VlaEx(TlaStr(_))
  private val validateRecordPair: Seq[TlaEx] => (String, TlaEx) = {
    // Only pairs coordinating pairs and sets are valid. See TlaSetOper.recSet
    case Seq(ValEx(TlaStr(name)), set) =>
      (name, set)

    case Seq(invalid, _) =>
      throw new IllegalArgumentException(s"Expected ValEx(TlaStr(_)) as a field name, found ${invalid}")

    case Seq(orphan) =>
      throw new IllegalArgumentException(s"Expected key-set pair, found ${orphan}")

    // since we group by 2 below, this case should be unreachable
    case moreThanTwo =>
      throw new IllegalArgumentException(
          s"Reached impossible state in validateRecSetPair: ${moreThanTwo}"
      )
  }

  /**
   * Translate an expression.
   *
   * @param ex a TLA expression
   * @return an expression in the simply typed lambda calculus variant Etc
   */
  def apply(ex: TlaEx): EtcExpr = {
    val tex = transform(ex)

    ex.typeTag match {
      case Typed(typeInTag: TlaType1) =>
        // the expression has a type tag `tt`.
        // To enforce this type, we introduce an intermediate operator application ((tt => tt) e).
        val identity = OperT1(Seq(typeInTag), typeInTag)
        val blameRef = BlameRef(ex.ID)
        mkApp(blameRef, Seq(identity), tex)

      case _ =>
        tex
    }
  }

  private def transform(ex: TlaEx): EtcExpr = {

    val ref = ExactRef(ex.ID)

    // Utility function to prepare the args needed for making an EtcApp expression
    def mkExRefApp(sig: OperT1, args: Seq[TlaEx]): EtcExpr = {
      mkApp(ref, Seq(sig), args.map(this(_)): _*)
    }

    ex match {
      case nm @ NameEx(_) =>
        // x becomes x
        mkName(nm)

      case ValEx(v) =>
        mkConst(ref, typeOfLiteralExpr(v))

      //******************************************** GENERAL OPERATORS **************************************************
      case OperEx(op, args @ _*) if op == TlaOper.eq || op == TlaOper.ne =>
        // x = y, x /= y
        val a = varPool.fresh
        val opsig = OperT1(Seq(a, a), BoolT1())
        mkExRefApp(opsig, args)

      case OperEx(TlaOper.apply, nameEx @ NameEx(_), args @ _*) =>
        // F(e_1, ..., e_n)
        mkAppByName(ref, mkName(nameEx), args.map(this(_)): _*)

      case OperEx(TlaOper.apply, opName, args @ _*) =>
        throw new TypingException(
            "Bug in ToEtcExpr. Expected an operator name, found: " + opName
        )

      case OperEx(
              TlaOper.chooseBounded,
              bindingNameEx @ NameEx(_),
              bindingSet,
              pred
          ) =>
        // CHOOSE x \in S: P
        // the principal type of CHOOSE is (a => Bool) => a
        val a = varPool.fresh
        val chooseType = OperT1(Seq(OperT1(Seq(a), BoolT1())), a)
        // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
        val chooseLambda =
          mkAbs(BlameRef(ex.ID), this(pred), (mkName(bindingNameEx), this(bindingSet)))
        // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
        mkApp(ref, Seq(chooseType), chooseLambda)

      case OperEx(TlaOper.chooseUnbounded, bindingNameEx @ NameEx(_), pred) =>
        // CHOOSE x: P
        // the principal type of CHOOSE is (a => Bool) => a
        //
        // Igor: I am not sure that this is a good solution, as the type checker will not propagate the possible
        // values of b from P. This expression will always give us a polytype.
        val a = varPool.fresh
        val chooseType = OperT1(Seq(OperT1(Seq(a), BoolT1())), a)
        // unbounded CHOOSE implicitly introduces a lambda abstraction: λ x ∈ Set(b). P
        val b = varPool.fresh
        val chooseLambda = mkAbs(
            BlameRef(ex.ID),
            this(pred),
            (mkName(bindingNameEx), mkConst(BlameRef(ex.ID), SetT1(b)))
        )
        // the resulting expression is (((a => Bool) => a) (λ x ∈ Set(b). P))
        mkApp(ref, Seq(chooseType), chooseLambda)

      //******************************************** LET-IN ****************************************************
      case LetInEx(body, declarations @ _*) =>
        val output =
          declarations.foldRight(this(body)) { case (decl, term) =>
            this(decl, term)
          }
        // to connect the uid of the LetInEx to the body, we wrap the output with an application of a nullary operator
        val a = varPool.fresh
        val identity = OperT1(Seq(a), a)
        mkApp(ref, Seq(identity), output)

      //******************************************** BOOLEANS **************************************************
      case OperEx(op, a, b) if op == TlaBoolOper.equiv || op == TlaBoolOper.implies =>
        // A <=> B, A => B
        val args = Seq(a, b)
        mkExRefApp(typeOfBoolOperArgs(args), args)

      case OperEx(op, args @ _*) if op == TlaBoolOper.and || op == TlaBoolOper.or =>
        // A /\ B /\ ... /\ C, A \/ B \/ ... \/ C
        mkExRefApp(typeOfBoolOperArgs(args), args)

      case OperEx(TlaBoolOper.not, arg) =>
        // ~A
        mkExRefApp(OperT1(Seq(BoolT1()), BoolT1()), Seq(arg))

      case OperEx(op, bindingEx, bindingSet, pred) if op == TlaBoolOper.exists || op == TlaBoolOper.forall =>
        // \E x \in S: P, \A x \in S: P
        // or, \E <<x, ..., z>> \in S: P

        // 1. When there is one argument, a set element has type "a", no tuple is involved.
        // 2. When there are multiple arguments,
        //    a set element has type type <<a, b>>, that is, it is a tuple.
        //    We can also have nested tuples like <<x, <<y, z>> >>, they are expanded.
        val bindings = translateBindings((bindingEx, bindingSet))
        val typeVars = varPool.fresh(bindings.length)
        // the principal type is ((a, b) => Bool) => Bool or just (a => Bool) => Bool
        val principal = OperT1(Seq(OperT1(typeVars, BoolT1())), BoolT1())
        // \E and \A implicitly introduce a lambda abstraction: λ x ∈ proj_x, y ∈ proj_y. P
        val lambda = mkAbs(BlameRef(ex.ID), this(pred), bindings: _*)
        // the resulting expression is (principal lambda)
        mkApp(ref, Seq(principal), lambda)

      //******************************************** SETS **************************************************
      case OperEx(TlaSetOper.enumSet) =>
        // empty set {} is not an operator but a constant
        val a = varPool.fresh
        mkConst(ref, SetT1(a))

      case OperEx(TlaSetOper.enumSet, args @ _*) =>
        // { 1, 2, 3 }
        val a = varPool.fresh
        val as = List.fill(args.length)(a)
        mkExRefApp(OperT1(as, SetT1(a)), args)

      case OperEx(TlaSetOper.funSet, args @ _*) =>
        // [S -> T]
        val a = varPool.fresh
        val b = varPool.fresh
        // (Set(a), Set(b)) => Set(a -> b)
        val sig = OperT1(Seq(SetT1(a), SetT1(b)), SetT1(FunT1(a, b)))
        mkExRefApp(sig, args)

      case OperEx(TlaSetOper.recSet, args @ _*) =>
        // [x: S, y: T]

        val (fields, sets) =
          args.grouped(2).map(validateRecordPair).toSeq.unzip

        val typeVars = varPool.fresh(sets.length)
        val recSetType = SetT1(RecT1(fields.zip(typeVars): _*))
        val opType = OperT1(typeVars.map(SetT1(_)), recSetType)
        mkExRefApp(opType, sets)

      case OperEx(TlaSetOper.seqSet, arg) =>
        // Seq(S)
        val a = varPool.fresh
        val sig = OperT1(Seq(SetT1(a)), SetT1(SeqT1(a)))
        mkExRefApp(sig, Seq(arg))

      case OperEx(op, args @ _*) if op == TlaSetOper.in || op == TlaSetOper.notin =>
        // x \in S, x \notin S
        val a = varPool.fresh
        val opsig = OperT1(List(a, SetT1(a)), BoolT1())
        mkExRefApp(opsig, args)

      case OperEx(op, args @ _*) if op == TlaSetOper.subseteq =>
        // S \subseteq T
        val a = varPool.fresh
        val opsig = OperT1(List(SetT1(a), SetT1(a)), BoolT1())
        mkExRefApp(opsig, args)

      case OperEx(TlaSetOper.SUBSET, args @ _*) =>
        // SUBSET S
        val a = varPool.fresh
        val opsig = OperT1(List(SetT1(a)), SetT1(SetT1(a)))
        mkExRefApp(opsig, args)

      case OperEx(TlaSetOper.union, args @ _*) =>
        // UNION S
        val a = varPool.fresh
        val opsig = OperT1(List(SetT1(SetT1(a))), SetT1(a))
        mkExRefApp(opsig, args)

      case OperEx(op, args @ _*) if op == TlaSetOper.cap || op == TlaSetOper.cup || op == TlaSetOper.setminus =>
        // S \\intersect T, S \\union T, S \\ T
        val a = varPool.fresh
        val opsig = OperT1(List(SetT1(a), SetT1(a)), SetT1(a))
        mkExRefApp(opsig, args)

      case OperEx(TlaSetOper.times, args @ _*) =>
        // S \X T
        val typeVars = varPool.fresh(args.length)
        val opsig = OperT1(typeVars.map(SetT1(_)), SetT1(TupT1(typeVars: _*)))
        mkExRefApp(opsig, args)

      case OperEx(TlaSetOper.filter, bindingEx, bindingSet, pred) =>
        // { x \in S: P }
        // or, { <<x, ..., z>> \in S: P }
        // the principal type is (a => Bool) => Set(a)
        val bindings = translateBindings((bindingEx, bindingSet))
        val typeVars = varPool.fresh(bindings.length)

        // 1. When there is one argument, a set element has type "a", no tuple is involved.
        // 2. When there are multiple arguments,
        //    a set element has type type <<a, b>>, that is, it is a tuple
        val funFrom =
          if (bindings.length == 1) typeVars.head else TupT1(typeVars: _*)
        // the principal type is ((a, b) => Bool) => Set(<<a, b>>) or just (a => Bool) => Set(a)
        val principal = OperT1(Seq(OperT1(typeVars, BoolT1())), SetT1(funFrom))

        // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. P
        val lambda = mkAbs(BlameRef(ex.ID), this(pred), bindings: _*)
        // the resulting expression is ((((a, b) => Bool) => Set(<<a, b>>)) (λ x ∈ S, y ∈ T. P)
        mkApp(ref, Seq(principal), lambda)

      case OperEx(TlaSetOper.map, mapExpr, args @ _*) =>
        // { x \in S, y \in T: e }
        val (vars, sets) = TlaOper.deinterleave(args)
        val bindings = translateBindings(vars zip sets: _*)
        val a = varPool.fresh
        val otherTypeVars =
          varPool.fresh(
              bindings.length
          ) // start with "b", as "a" goes to the result
        // the principal type of is ((b, c) => a) => Set(a)
        val principal = OperT1(Seq(OperT1(otherTypeVars, a)), SetT1(a))
        // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
        val lambda = mkAbs(BlameRef(mapExpr.ID), this(mapExpr), bindings: _*)
        mkApp(ref, Seq(principal), lambda)

      //******************************************** FUNCTIONS **************************************************
      case OperEx(TlaFunOper.enum, args @ _*) =>
        // [f1 |-> e1, f2 |-> e2]
        val (fields, values) =
          args.grouped(2).map(validateRecordPair).toSeq.unzip
        val typeVars = varPool.fresh(fields.length)
        // (a, b) => [f1 |-> a, f2 |-> b]
        val sig = OperT1(typeVars, RecT1(fields.zip(typeVars): _*))
        mkExRefApp(sig, values)

      case OperEx(TlaFunOper.tuple) =>
        // an empty sequence << >> is not an operator, but a polymorphic constant
        mkConst(ref, SeqT1(varPool.fresh))

      case OperEx(TlaFunOper.tuple, args @ _*) =>
        // <<e_1, ..., e_n>>
        val typeVars = varPool.fresh(args.length)
        val a = if (typeVars.nonEmpty) typeVars.head else varPool.fresh
        val values = args.map(this(_))
        val tuple = OperT1(typeVars, TupT1(typeVars: _*))
        val as = List.fill(args.length)(a)
        val seq = OperT1(as, SeqT1(a))
        mkApp(ref, Seq(tuple, seq), values: _*)

      case OperEx(TlaFunOper.app, fun, arg) =>
        // f[e], where f can be one of: a function, a record, a tuple, or a sequence
        val signatures = mkFunLikeByArg(arg).map { case (funType, argType, resType) =>
          OperT1(Seq(funType, argType), resType)
        }
        mkApp(ref, signatures, this(fun), this(arg))

      case OperEx(TlaFunOper.domain, fun) =>
        // DOMAIN f
        val a = varPool.fresh
        val b = varPool.fresh
        val funType = OperT1(Seq(FunT1(a, b)), SetT1(a)) // (a -> b) => Set(a)
        val seqType =
          OperT1(Seq(SeqT1(a)), SetT1(IntT1())) // Seq(a) => Set(Int)
        val recType = OperT1(Seq(RecT1()), SetT1(StrT1())) // [] => Set(Str)
        val tupType =
          OperT1(Seq(SparseTupT1()), SetT1(IntT1())) // {} => Set(Int)
        mkApp(
            ref,
            Seq(funType, seqType, recType, tupType),
            this(fun)
        )

      case OperEx(TlaFunOper.funDef, mapExpr, args @ _*) =>
        // [ x \in S, y \in T |-> e ]
        // or, [ <<x, y>> \in S, z \in T |-> e ]
        val bindings =
          translateBindings(
              args
                .grouped(2)
                .map {
                  case Seq(varEx, setEx) => (varEx, setEx)
                  case orphan            => throw new TypingException(s"Invalid bound variables and sets ${orphan} in: ${ex}")
                }
                .toSeq: _*
          )

        val a = varPool.fresh
        // start with "b", as "a" goes to the result
        val typeVars = varPool.fresh(bindings.length)

        val funFrom = typeVars match {
          // With one argument, the generated function has the type b -> a, that is, no tuple is involved.
          case Seq(v) => v
          // With multiple arguments, the generated function has the type <<b, c>> -> a, that is, it accepts a tuple
          case _ => TupT1(typeVars: _*)
        }

        // The principal type is ((b, c) => a) => (<<b, c>> -> a).
        // Note that the generated function has the type <<b, c>> -> a, that is, it accepts a tuple.
        val principal = OperT1(Seq(OperT1(typeVars, a)), FunT1(funFrom, a))
        // the function definition implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
        val lambda = mkAbs(BlameRef(mapExpr.ID), this(mapExpr), bindings: _*)
        mkApp(ref, Seq(principal), lambda)

      case OperEx(TlaFunOper.except, fun, args @ _*) =>
        // The hardest expression: [f EXCEPT ![e1] = e2, ![e3] = e4, ...]
        val (accessors, newValues) = TlaOper.deinterleave(args)

        // generate the expressions for (e_1, e_2), ..., (e_{n-1}, e_n)
        val towersOfUnapply: Seq[EtcExpr] = accessors.zip(newValues).map(p => mkUnapplyForExcept(p._1, p._2))

        // To guarantee that the function and the updates have the same types, produce (c, ..., c) => c
        val a = varPool.fresh
        val nargs = accessors.length + 1
        val sig = OperT1(1.to(nargs) map { _ => a }, a)
        mkApp(ref, Seq(sig), this(fun) +: towersOfUnapply: _*)

      case funDef @ OperEx(TlaFunOper.recFunDef, body, args @ _*) =>
        // fun[x \in S, y \in T |-> e] == ...
        // or, fun[<<x, y>> \in S, z \in T |-> e] == ...
        //
        // We give the example for a one-argument function, as the case of multiple arguments is complex:
        // (((b -> a) => (b => a)) => (b -> a)) (λ $recFun ∈ Set(c -> d). λ x ∈ Int. x)
        val bindings =
          translateBindings(
              args
                .grouped(2)
                .map {
                  case Seq(varEx, setEx) => (varEx, setEx)
                  case orphan            => throw new TypingException(s"Invalid bound variables and sets ${orphan} in: ${ex}")
                }
                .toSeq: _*
          )

        val resultType = varPool.fresh
        val argTypes = varPool.fresh(bindings.length)

        // wrap multiple variables into a tuple, while keeping a single variable unwrapped
        def mkFunFrom: Seq[VarT1] => TlaType1 = {
          // With one argument, the generated function has the type b -> a, that is, no tuple is involved.
          case Seq(one) => one
          // With multiple arguments, the generated function has the type <<b, c>> -> a, that is, it accepts a tuple
          case many => TupT1(many: _*)
        }

        // e.g., b -> a, or <<b, c>> -> a
        val funType = FunT1(mkFunFrom(argTypes), resultType)
        // e.g., b => a, or (b, c) => a
        val operType = OperT1(argTypes, resultType)
        val principal = OperT1(Seq(OperT1(Seq(funType), operType)), funType)
        // λ x ∈ S, y ∈ T. [[body]]
        val innerLambda = mkAbs(BlameRef(body.ID), this(body), bindings: _*)
        // create another vector of type variables for the lambda over a function
        val recFunResTypeVar = varPool.fresh
        val resFunArgTypes = mkFunFrom(varPool.fresh(bindings.length))
        val funRefByName = mkName(BlameRef(funDef.ID), TlaFunOper.recFunRef.uniqueName)
        val outerLambda = mkAbs(
            BlameRef(ex.ID),
            innerLambda,
            (
                funRefByName,
                mkConst(BlameRef(ex.ID), SetT1(FunT1(resFunArgTypes, recFunResTypeVar)))
            )
        )
        mkApp(ref, Seq(principal), outerLambda)

      case OperEx(TlaFunOper.recFunRef) =>
        mkName(ref, TlaFunOper.recFunRef.uniqueName)

      //******************************************** CONTROL **************************************************

      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        // IF e1 THEN e2 ELSE E2
        // (Bool, a, a) => a
        val a = varPool.fresh
        val opsig = OperT1(List(BoolT1(), a, a), a)
        mkExRefApp(opsig, Seq(predEx, thenEx, elseEx))

      case OperEx(op, args @ _*) if op == TlaControlOper.caseNoOther || op == TlaControlOper.caseWithOther =>
        // CASE p1 -> e1 [] p2 -> e2
        // CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3
        val nargs = args.length
        val nargs2 =
          (args.length / 2) * 2 // the largest even number below nargs
        // Bool, a, Bool, a, ...
        val a = varPool.fresh
        val boolAndAs =
          0.until(nargs2).map(i => if (i % 2 == 0) BoolT1() else a)
        val operArgs = if (nargs % 2 == 1) a +: boolAndAs else boolAndAs
        val opsig = OperT1(operArgs, a)
        mkExRefApp(opsig, args)

      //******************************************** FiniteSets ************************************************
      case OperEx(TlaFiniteSetOper.isFiniteSet, setEx) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SetT1(a)), BoolT1()) // Set(a) => Bool
        mkExRefApp(opsig, Seq(setEx))

      case OperEx(TlaFiniteSetOper.cardinality, setEx) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SetT1(a)), IntT1()) // Set(a) => Int
        mkExRefApp(opsig, Seq(setEx))

      //*************************************** ACTION OPERATORS ***********************************************
      case OperEx(TlaActionOper.prime, inner) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(a), a) // a => a
        mkExRefApp(opsig, Seq(inner))

      case OperEx(op, args @ _*) if op == TlaActionOper.stutter || op == TlaActionOper.nostutter =>
        // Bool, a, b, c => Bool
        val opsig = OperT1(BoolT1() +: varPool.fresh(args.length - 1), BoolT1())
        mkExRefApp(opsig, args)

      case OperEx(TlaActionOper.enabled, inner) =>
        val opsig = OperT1(Seq(BoolT1()), BoolT1()) // Bool => Bool
        mkExRefApp(opsig, Seq(inner))

      // feature #660: special treatment for UNCHANGED <<...>>, as it is so common
      case OperEx(TlaActionOper.unchanged, tex @ OperEx(TlaFunOper.tuple, args @ _*)) =>
        val typeVars = varPool.fresh(args.length)
        // the principal type is: (<<a_1, ..., a_n>> => Bool) ((a_1, ..., a_n) => <<a_1, ..., a_n>>)
        val tupleType = TupT1(typeVars: _*)
        val tupleOperType = OperT1(typeVars, tupleType)
        // (a_1, ..., a_n) => <<a_1, ..., a_n>>
        val tupleEx = mkApp(ExactRef(tex.ID), Seq(tupleOperType), args.map(this(_)): _*)
        // <<a_1, ..., a_n>> => Bool
        val opsig = OperT1(Seq(tupleType), BoolT1())
        mkApp(ExactRef(ex.ID), Seq(opsig), tupleEx)

      case OperEx(TlaActionOper.unchanged, args @ _*) =>
        val opsig =
          OperT1(varPool.fresh(args.length), BoolT1()) // a, b, c => Bool
        mkExRefApp(opsig, args)

      case OperEx(TlaActionOper.composition, a, b) =>
        val opsig =
          OperT1(Seq(BoolT1(), BoolT1()), BoolT1()) // (Bool, Bool) => Bool
        mkExRefApp(opsig, Seq(a, b))

      //******************************************** Sequences *************************************************
      case OperEx(TlaSeqOper.head, s) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SeqT1(a)), a) // Seq(a) => a
        mkExRefApp(opsig, Seq(s))

      case OperEx(TlaSeqOper.tail, s) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SeqT1(a)), SeqT1(a)) // Seq(a) => Seq(a)
        mkExRefApp(opsig, Seq(s))

      case OperEx(TlaSeqOper.append, args @ _*) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SeqT1(a), a), SeqT1(a)) // Seq(a), a => Seq(a)
        mkExRefApp(opsig, args)

      case OperEx(TlaSeqOper.concat, s, t) =>
        val a = varPool.fresh
        val opsig =
          OperT1(Seq(SeqT1(a), SeqT1(a)), SeqT1(a)) // Seq(a), Seq(a) => Seq(a)
        mkExRefApp(opsig, Seq(s, t))

      case OperEx(TlaSeqOper.len, s) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SeqT1(a)), IntT1()) // Seq(a) => Int
        mkExRefApp(opsig, Seq(s))

      case OperEx(TlaSeqOper.subseq, args @ _*) =>
        val a = varPool.fresh
        val opsig =
          OperT1(
              Seq(SeqT1(a), IntT1(), IntT1()),
              SeqT1(a)
          ) // Seq(a), Int, Int => Seq(a)
        mkExRefApp(opsig, args)

      case OperEx(TlaSeqOper.selectseq, args @ _*) =>
        val a = varPool.fresh
        val filter = OperT1(Seq(a), BoolT1())
        val opsig =
          OperT1(
              Seq(SeqT1(a), filter),
              SeqT1(a)
          ) // Seq(a), (a => Bool) => Seq(a)
        mkExRefApp(opsig, args)

      //******************************************** INTEGERS **************************************************
      case OperEx(TlaArithOper.uminus, args @ _*) =>
        // -x
        val opsig = OperT1(Seq(IntT1()), IntT1())
        mkExRefApp(opsig, args)

      case OperEx(op, args @ _*)
          if op == TlaArithOper.plus || op == TlaArithOper.minus || op == TlaArithOper.mult
            || op == TlaArithOper.div || op == TlaArithOper.mod || op == TlaArithOper.exp =>
        // x + y, x - y, x * y, x \div y, x % y, x^y
        val opsig = OperT1(List(IntT1(), IntT1()), IntT1())
        mkExRefApp(opsig, args)

      case OperEx(op, args @ _*)
          if op == TlaArithOper.lt || op == TlaArithOper.le || op == TlaArithOper.gt || op == TlaArithOper.ge =>
        // x < y, x <= y, x > y, x >= y
        val opsig = OperT1(List(IntT1(), IntT1()), BoolT1())
        mkExRefApp(opsig, args)

      case OperEx(TlaArithOper.dotdot, args @ _*) =>
        // a..b
        val opsig = OperT1(List(IntT1(), IntT1()), SetT1(IntT1()))
        mkExRefApp(opsig, args)

      case OperEx(TlaArithOper.realDiv, args @ _*) =>
        // a / b
        val opsig = OperT1(List(RealT1(), RealT1()), RealT1())
        mkExRefApp(opsig, args)

      //***************************************** TEMPORAL *************************************************
      case OperEx(op, inner) if op == TlaTempOper.box || op == TlaTempOper.diamond =>
        val opsig = OperT1(Seq(BoolT1()), BoolT1()) // Bool => Bool
        mkExRefApp(opsig, Seq(inner))

      case OperEx(op, lhs, rhs) if op == TlaTempOper.guarantees || op == TlaTempOper.leadsTo =>
        val opsig =
          OperT1(Seq(BoolT1(), BoolT1()), BoolT1()) // (Bool, Bool) => Bool
        mkExRefApp(opsig, Seq(lhs, rhs))

      case OperEx(op, sub, act) if op == TlaTempOper.weakFairness || op == TlaTempOper.strongFairness =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(a, BoolT1()), BoolT1()) // (a, Bool) => Bool
        mkExRefApp(opsig, Seq(sub, act))

      //******************************************** Apalache **************************************************
      case OperEx(ApalacheOper.funAsSeq, fun, len) =>
        val a = varPool.fresh
        // ((Int -> a), Int) => Seq(a)
        val opsig = OperT1(Seq(FunT1(IntT1(), a), IntT1()), SeqT1(a))
        mkExRefApp(opsig, Seq(fun, len))

      case OperEx(ApalacheOper.gen, bound) =>
        val a = varPool.fresh
        // Int => a
        val opsig = OperT1(Seq(IntT1()), a)
        mkExRefApp(opsig, Seq(bound))

      case OperEx(ApalacheOper.assign, lhs, rhs) =>
        val a = varPool.fresh
        // (a, a) => Bool
        val opsig = OperT1(Seq(a, a), BoolT1())
        mkExRefApp(opsig, Seq(lhs, rhs))

      case OperEx(ApalacheOper.expand, set) =>
        val a = varPool.fresh
        // a => Bool
        val opsig = OperT1(Seq(a), a)
        mkExRefApp(opsig, Seq(set))

      case OperEx(ApalacheOper.skolem, predicate) =>
        // Bool => Bool
        val opsig = OperT1(Seq(BoolT1()), BoolT1())
        mkExRefApp(opsig, Seq(predicate))

      case OperEx(ApalacheOper.constCard, predicate) =>
        // Bool => Bool
        val opsig = OperT1(Seq(BoolT1()), BoolT1())
        mkExRefApp(opsig, Seq(predicate))

      case OperEx(ApalacheOper.distinct, args @ _*) =>
        val a = varPool.fresh
        // (a, ..., a) => Bool
        val opsig = OperT1(args.map(_ => a), BoolT1())
        mkExRefApp(opsig, args)

      //******************************************** MISC **************************************************
      case OperEx(TlaOper.label, labelledEx, nameAndArgs @ _*) =>
        val typeVar = varPool.fresh
        mkExRefApp(OperT1(nameAndArgs.map(_ => StrT1()) :+ typeVar, typeVar), nameAndArgs :+ labelledEx)

      case OperEx(ApalacheOper.withType, lhs, annotation) =>
        // Met an old type annotation. Warn the user and ignore the annotation.
        logger.error("Met an old type annotation: " + annotation)
        logger.error("See: https://apalache.informal.systems/docs/apalache/typechecker-snowcat.html")
        val msg = s"Old Apalache type annotations (predating 0.12.0) are no longer supported"
        throw new OutdatedAnnotationsError(msg, ex)

      //********************************************* TLC **************************************************
      case OperEx(TlcOper.print, text, value) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(StrT1(), a), StrT1()) // (Str, a) => Str
        mkExRefApp(opsig, Seq(text, value))

      case OperEx(TlcOper.printT, text) =>
        val opsig = OperT1(Seq(StrT1()), BoolT1()) // Str => Bool
        mkExRefApp(opsig, Seq(text))

      case OperEx(TlcOper.assert, value, text) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(a, StrT1()), BoolT1()) // (a, Str) => Bool
        mkExRefApp(opsig, Seq(value, text))

      case OperEx(TlcOper.javaTime) =>
        val opsig = OperT1(Seq(), IntT1()) // () => Int
        mkExRefApp(opsig, Seq())

      case OperEx(TlcOper.tlcGet, index) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(IntT1()), a) // Int => a
        mkExRefApp(opsig, Seq(index))

      case OperEx(TlcOper.tlcSet, index, value) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(IntT1(), a), BoolT1()) // (Int, a) => Bool
        mkExRefApp(opsig, Seq(index, value))

      case OperEx(TlcOper.colonGreater, key, value) =>
        val a = varPool.fresh
        val b = varPool.fresh
        val opsig = OperT1(Seq(a, b), FunT1(a, b)) // (a, b) => (a -> b)
        mkExRefApp(opsig, Seq(key, value))

      case OperEx(TlcOper.atat, f1, f2) =>
        val a = varPool.fresh
        val b = varPool.fresh
        val opsig = OperT1(Seq(FunT1(a, b), FunT1(a, b)), FunT1(a, b)) // (a -> b, a -> b) => (a -> b)
        mkExRefApp(opsig, Seq(f1, f2))

      case OperEx(TlcOper.permutations, set) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SetT1(a)), SetT1(FunT1(a, a))) // Set(a) => Set(a -> a)
        mkExRefApp(opsig, Seq(set))

      case OperEx(TlcOper.sortSeq, seq, op) =>
        val a = varPool.fresh
        // (Seq(a), ((a, a) => Bool)) => Seq(a)
        val opsig = OperT1(Seq(SeqT1(a), OperT1(Seq(a, a), BoolT1())), SeqT1(a))
        mkExRefApp(opsig, Seq(seq, op))

      case OperEx(TlcOper.randomElement, set) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(SetT1(a)), a) // Set(a) => a
        mkExRefApp(opsig, Seq(set))

      case OperEx(TlcOper.any) =>
        // We are adding the signature of this operator, but it is pretty useless.
        // The type checker will most probably complain about the type variable 'a'.
        val a = varPool.fresh
        val opsig = OperT1(Seq(), a) // () => a
        mkExRefApp(opsig, Seq())

      case OperEx(TlcOper.tlcToString, value) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(a), StrT1()) // a => Str
        mkExRefApp(opsig, Seq(value))

      case OperEx(TlcOper.tlcEval, value) =>
        val a = varPool.fresh
        val opsig = OperT1(Seq(a), a) // a => a
        mkExRefApp(opsig, Seq(value))

      // This should be unreachable
      case expr =>
        throw new IllegalArgumentException(s"Unsupported expression: ${expr}")
    }
  }

  /**
   * Usually, one uses bindings like x \in S, y \in T in set comprehensions and function definitions.
   * However, TLA+ allows for advanced syntax in bindings, e.g., << x, y >> \in S, << u, << v, w >> >> \in T.
   * This method does a general translation for variable bindings
   *
   * @param bindings pairs of expressions, e.g., (NameEx("x"), NameEx("S"))
   * @return translated bindings, where all tuples have been unpacked
   */
  private def translateBindings(
      bindings: (TlaEx, TlaEx)*
  ): Seq[(EtcName, EtcExpr)] = {
    // Project a tuple and a set of dim-tuples on the ith element (starting with 0!).
    // We have to pass a tuple as well, in order to back-propagate the type later.
    def project(id: UID, tupleId: UID, setEx: EtcExpr, dim: Int, index: Int): EtcExpr = {
      val typeVars = varPool.fresh(dim)
      val tupleType = TupT1(typeVars: _*)
      // e.g., (<<a, b, c>>, Set(<<a, b, c>>)) => Set(b)
      val operType =
        OperT1(Seq(tupleType, SetT1(tupleType)), SetT1(typeVars(index)))
      // passing tupleConst is crucial, to be able to recover the type of the tuple later
      val tupleConst = mkConst(ExactRef(tupleId), tupleType)
      // (operType tupleType set)
      mkApp(BlameRef(id), Seq(operType), tupleConst, setEx)
    }

    def unpackOne(
        id: UID, target: TlaEx, set: EtcExpr
    ): Seq[(EtcName, EtcExpr)] = {
      target match {
        // simplest case: name is bound to set
        case nameEx @ NameEx(_) =>
          Seq((mkName(nameEx), set))

        // advanced case: <<x, y, ..., z>> is bound to set
        case OperEx(TlaFunOper.tuple, args @ _*) =>
          args.zipWithIndex.flatMap { case (a, i) =>
            unpackOne(id, a, project(id, target.ID, set, args.length, i))
          }

        case _ =>
          throw new TypingInputException(
              s"Unexpected binding $target \\in $set"
          )
      }
    }

    // unpack x \in S, <<y, z>> \in T into x \in S, y \in project(T, 1), z \in project(T, 2)
    bindings.flatMap { case (target, set) =>
      unpackOne(set.ID, target, this(set))
    }
  }

  // Translate a sequence of formal parameters into type variables
  private def formalParamsToTypeVars(
      params: Seq[FormalParam]
  ): Seq[(String, TlaType1)] = {
    params match {
      case Seq() => Seq()

      case SimpleFormalParam(name) +: tail =>
        // a simple parameter, just introduce a new variable, e.g., b
        val paramType = varPool.fresh
        (name, paramType) +: formalParamsToTypeVars(tail)

      case OperFormalParam(name, arity) +: tail =>
        // a higher-order operator, introduce an operator type (b, c, ...) => z
        val paramType = OperT1(varPool.fresh(arity), varPool.fresh)
        (name, paramType) +: formalParamsToTypeVars(tail)
    }
  }

  // translate [f EXCEPT ![i_1]...[i_n] = e], which can be used to translate the general case
  private def mkUnapplyForExcept(accessorTuple: TlaEx, value: TlaEx): EtcExpr = {
    val indices = accessorTuple match {
      case OperEx(TlaFunOper.tuple, elems @ _*) =>
        elems

      case e =>
        // this is an internal error of the intermediate representation
        throw new IllegalArgumentException("Expected a tuple as an accessor in EXCEPT, found: " + e)
    }

    // The trick here is to eat the indices from the tail, as the choice of types depends on the indices.
    // This is somewhat similar to unapply in Scala.
    indices.foldRight(this(value)) { case (index, result) =>
      val options = mkFunLikeByArg(index)
      val signatures = options.map(t => OperT1(Seq(t._2, t._3), t._1))
      // ((a, b) => a -> b) index result)
      mkApp(BlameRef(index.ID), signatures, this(index), result)
    }
  }

  // look at at the argument of a function-like expression (function, record, tuple, or sequence)
  // and return the possible options of: (funType, argType, resType)
  private def mkFunLikeByArg(arg: TlaEx): Seq[(TlaType1, TlaType1, TlaType1)] = {
    arg match {
      case ValEx(TlaInt(fieldNo)) =>
        // f[i] or [f EXCEPT ![i] = ...], where i is an integer literal
        val a = varPool.fresh
        Seq(
            // ((Int -> a), Int) => a
            (FunT1(IntT1(), a), IntT1(), a),
            // (Seq(a), Int) => a
            (SeqT1(a), IntT1(), a),
            // ({ 3: a }, Int) => a
            (SparseTupT1(fieldNo.toInt -> a), IntT1(), a)
        )

      case ValEx(TlaStr(fieldName)) =>
        // f[s] or [f EXCEPT ![s] = ...], where s is a string literal
        val a = varPool.fresh
        Seq(
            // ((Str -> a), Str) => a
            (FunT1(StrT1(), a), StrT1(), a),
            // ([ foo: a ], Str) => a
            (RecT1(fieldName -> a), StrT1(), a)
        )

      case _ =>
        // the general case of f[e] or [f EXCEPT ![e] = ...]
        val a = varPool.fresh
        val b = varPool.fresh
        Seq(
            // ((a -> b), a) => b
            (FunT1(a, b), a, b),
            // (Seq(a), Int) => a
            (SeqT1(a), IntT1(), a)
        )
    }
  }

  private def mkName(nameEx: NameEx): EtcName = {
    mkName(ExactRef(nameEx.ID), nameEx.name)
  }

  private def renameVars(tt: TlaType1): TlaType1 = {
    val varRenamingMap = tt.usedNames.toSeq.map(i => i -> varPool.fresh)
    Substitution(varRenamingMap: _*)(tt)
  }
}

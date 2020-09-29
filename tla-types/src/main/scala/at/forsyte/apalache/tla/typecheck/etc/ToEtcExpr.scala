package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.parser.{DefaultType1Parser, Type1ParseError}

/**
  * ToSTCExpr takes a TLA+ expression and produces an STCExpr.
  * The most interesting part of this translation is dealing with the built-in operators.
  * This translator is an extension of the ideas that appear in SignatureGenerator by Jure Kukovec.
  *
  * @see at.forsyte.apalache.tla.types.SignatureGenerator
  *
  * @author Igor Konnov
  */
class ToEtcExpr(varPool: TypeVarPool) extends EtcBuilder {
  private val type1Parser = DefaultType1Parser
  /**
    * The counter that we use to produce fresh variables
    */
  private var nextVarNum = 0

  /**
    * Get the number just above the maximum variable number
    * @return an upper bound on the variable numbers
    */
  def varNumUpperBound: Int = nextVarNum

  /**
    * Translate an operator declaration.
    *
    * @param decl an operator declaration
    * @param inScopeEx an expression to chain in the bottom of let-definition, it should have been translated
    * @return the translated let-in expression with inScopeEx attached
    */
  def apply(decl: TlaOperDecl, inScopeEx: EtcExpr): EtcExpr = {
    if (decl.name.startsWith("TypeAssumptions")) {
      // the special form for type annotations over state variables and constants
      parseTypeAssumptions(decl, inScopeEx)
    } else {
      // The type of the lambda is what we want to see as the type of the declaration.
      // There are two cases: (1) the definition body contains a type annotation, and (2) no type annotation
      val paramsAndDoms = formalParamsToTypeVars(decl.formalParams).map {
        case (paramName, paramType) =>
          (paramName, mkConst(BlameRef(decl.body.ID), SetT1(paramType)) )
      }

      decl.body match {
        case OperEx(TypingOper.withType, ValEx(TlaStr(typeText)), body) =>
          // case 1: the definition body contains a type annotation
          val parsedType =
            try {
              renameVars(type1Parser(typeText))
            } catch {
              case e: Type1ParseError =>
                throw new TypingInputException(s"Parser error in type annotation of ${decl.name}: ${e.msg}")
            }

          val lambda = mkAbs(ExactRef(body.ID), this (body), paramsAndDoms: _*)
          val letIn = mkLet(BlameRef(body.ID), decl.name, lambda, inScopeEx)
          mkTypeDecl(ExactRef(decl.body.ID), decl.name, parsedType, letIn)

        case _ =>
          // case 2: no type annotation
          val lambda = mkAbs(ExactRef(decl.body.ID), this (decl.body), paramsAndDoms: _*)
          mkLet(BlameRef(decl.body.ID), decl.name, lambda, inScopeEx)
      }
    }
  }

  // parse the type annotations inside TypeAssumptions
  private def parseTypeAssumptions(decl: TlaOperDecl, inScopeEx: EtcExpr): EtcExpr = {
    decl.body match {
      case OperEx(TlaBoolOper.and, args @ _*) =>
        val annotations =
          args.collect { case OperEx(TypingOper.assumeType, NameEx(name), ValEx(TlaStr(typeText))) =>  (name, typeText) }
        if (annotations.length != args.length) {
          throw new TypingInputException(s"""Error in ${decl.name}: Expected AssumeType(varName, "typeString")""")
        } else {
          annotations.foldRight(inScopeEx) {
            case ((name, typeText), terminal) =>
              try {
                val tt = renameVars(type1Parser(typeText))
                mkTypeDecl(ExactRef(decl.body.ID), name, tt, terminal)
              } catch {
                case e: Type1ParseError =>
                  throw new TypingInputException(s"Parser error in type annotation of $name: ${e.msg}")
              }
          }
        }

      case _ =>
        throw new TypingInputException(s"""Error in ${decl.name}: Expected /\ AssumeType(varName, "typeString") /\ ...""")
    }
  }

  // TODO: a long string of translation rules. Can we decompose it?
  def apply(ex: TlaEx): EtcExpr = ex match {
    case NameEx(name) =>
      // x becomes x
      mkName(ExactRef(ex.ID), name)

    //*********************************************** LITERALS **************************************************
    case ValEx(TlaInt(_)) =>
      // an integer literal becomes IntT1
      mkConst(ExactRef(ex.ID), IntT1())

    case ValEx(TlaBool(_)) =>
      // a Boolean literal becomes BoolT1
      mkConst(ExactRef(ex.ID), BoolT1())

    case ValEx(TlaStr(_)) =>
      // a string literal becomes StrT1
      mkConst(ExactRef(ex.ID), StrT1())

    case ValEx(TlaReal()) =>
      // a real literal becomes RealT1
      mkConst(ExactRef(ex.ID), RealT1())

    case ValEx(TlaIntSet) =>
      // the set of all integers is SetT1(IntT1)
      mkConst(ExactRef(ex.ID), SetT1(IntT1()))

    case ValEx(TlaNatSet) =>
      // the set of all naturals is SetT1(IntT1)
      mkConst(ExactRef(ex.ID), SetT1(IntT1()))

    case ValEx(TlaRealSet) =>
      // the set of all reals is SetT1(RealT1)
      mkConst(ExactRef(ex.ID), SetT1(RealT1()))

    case ValEx(TlaBoolSet) =>
      // the set of all Booleans is SetT1(BoolT1)
      mkConst(ExactRef(ex.ID), SetT1(BoolT1()))

    case ValEx(TlaStrSet) =>
      // the set of all strings is SetT1(StrT1)
      mkConst(ExactRef(ex.ID), SetT1(StrT1()))

    //**************************************** EMPTY SETS AND SEQUENCES ***********************************************
    case OperEx(TypingOper.emptySet, ValEx(TlaStr(elemTypeText))) =>
      try {
        val elemType = renameVars(type1Parser(elemTypeText))
        mkConst(ExactRef(ex.ID), SetT1(elemType))
      } catch {
        case e: Type1ParseError =>
          throw new TypingInputException(s"Parser error in Typing!EmptySet($elemTypeText): ${e.msg}")
      }

    case OperEx(TypingOper.emptySeq, ValEx(TlaStr(elemTypeText))) =>
      try {
        val elemType = renameVars(type1Parser(elemTypeText))
        mkConst(ExactRef(ex.ID), SeqT1(elemType))
      } catch {
        case e: Type1ParseError =>
          throw new TypingInputException(s"Parser error in Typing!EmptySeq($elemTypeText): ${e.msg}")
      }

    //******************************************** GENERAL OPERATORS **************************************************
    case OperEx(op, args @ _*) if op == TlaOper.eq || op == TlaOper.ne =>
      // x = y, x /= y
      val a = varPool.fresh
      val opsig = OperT1(Seq(a, a), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaOper.apply, NameEx(name), args @ _*) =>
      // F(e_1, ..., e_n)
      mkAppByName(ExactRef(ex.ID), name, args.map(this(_)) :_*)

    case OperEx(TlaOper.apply, opName, args @ _*) =>
      throw new TypingException("Bug in ToSTCExpr. Expected an operator name, found: " + opName)

    case OperEx(TlaOper.chooseBounded, NameEx(bindingVar), bindingSet, pred) =>
      // CHOOSE x \in S: P
      // the principal type of CHOOSE is (a => Bool) => a
      val a = varPool.fresh
      val chooseType = OperT1(Seq(OperT1(Seq(a), BoolT1())), a)
      // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
      val chooseLambda = mkAbs(BlameRef(ex.ID), this(pred), (bindingVar, this(bindingSet)))
      // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
      mkApp(ExactRef(ex.ID), Seq(chooseType), chooseLambda)

    case OperEx(TlaOper.chooseUnbounded, NameEx(bindingVar), pred) =>
      // CHOOSE x: P
      // the principal type of CHOOSE is (a => Bool) => a
      //
      // Igor: I am not sure that this is a good solution, as the type checker will not propagate the possible
      // values of b from P. This expression will always give us a polytype.
      val a = varPool.fresh
      val chooseType = OperT1(Seq(OperT1(Seq(a), BoolT1())), a)
      // unbounded CHOOSE implicitly introduces a lambda abstraction: λ x ∈ Set(b). P
      val b = varPool.fresh
      val chooseLambda = mkAbs(BlameRef(ex.ID), this(pred),
        (bindingVar, mkConst(BlameRef(ex.ID), SetT1(b))))
      // the resulting expression is (((a => Bool) => a) (λ x ∈ Set(b). P))
      mkApp(ExactRef(ex.ID), Seq(chooseType), chooseLambda)

    //******************************************** LET-IN ****************************************************
    case LetInEx(body, declarations @ _*) =>
      declarations.foldRight(this(body)) { case (decl, term) => this(decl, term) }

    //******************************************** BOOLEANS **************************************************
    case OperEx(op, args @ _*)
        if op == TlaBoolOper.and || op == TlaBoolOper.or || op == TlaBoolOper.equiv || op == TlaBoolOper.implies =>
      // A /\ B, A \/ B, A <=> B, A => B
      val nBools = List.fill(args.length)(BoolT1())
      val opsig = OperT1(nBools, BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaBoolOper.not, arg) =>
      // ~A
      mkApp(ex.ID, OperT1(Seq(BoolT1()), BoolT1()), Seq(arg))

    case OperEx(op, NameEx(bindingVar), bindingSet, pred)
        if op == TlaBoolOper.exists || op == TlaBoolOper.forall =>
      // \E x \in S: P, \A x \in S: P
      // the principal type of \A and \E is (a => Bool) => Bool
      val a = varPool.fresh
      val quantType = OperT1(Seq(OperT1(Seq(a), BoolT1())), BoolT1())
      // \E and \A implicitly introduce a lambda abstraction: λ x ∈ S. P
      val lambda = mkAbs(BlameRef(ex.ID), this(pred), (bindingVar, this(bindingSet)))
      // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
      mkApp(ExactRef(ex.ID), Seq(quantType), lambda)

    //******************************************** SETS **************************************************
    case OperEx(TlaSetOper.enumSet) =>
      // empty set {} is not an operator but a constant
      val a = varPool.fresh
      mkConst(ExactRef(ex.ID), SetT1(a))

    case OperEx(TlaSetOper.enumSet, args @ _*) =>
      // { 1, 2, 3 }
      val a = varPool.fresh
      val as = List.fill(args.length)(a)
      mkApp(ex.ID, OperT1(as, SetT1(a)), args)

    case OperEx(TlaSetOper.funSet, args @ _*) =>
      // [S -> T]
      val a = varPool.fresh
      val b = varPool.fresh
      // (Set(a), Set(b)) => Set(a -> b)
      val sig = OperT1(Seq(SetT1(a), SetT1(b)), SetT1(FunT1(a, b)))
      mkApp(ex.ID, sig, args)

    case OperEx(TlaSetOper.recSet, args @ _*) =>
      // [x: S, y: T]
      val fields = args.zipWithIndex.collect {
        case (ValEx(TlaStr(name)), i) if i % 2 == 0 => name
        case (_, i) if i % 2 == 0 => throw new IllegalArgumentException("Expected ValEx(TlaStr(_)) as a field name")
      }
      val sets = args.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
      val typeVars = varPool.fresh(sets.length)
      val recSetType = SetT1(RecT1(fields.zip(typeVars) :_*))
      val opType = OperT1(typeVars.map(SetT1(_)), recSetType)
      mkApp(ex.ID, opType, sets)

    case OperEx(TlaSetOper.seqSet, arg) =>
      // Seq(S)
      val a = varPool.fresh
      val sig = OperT1(Seq(SetT1(a)), SeqT1(a))
      mkApp(ex.ID, sig, Seq(arg))

    case OperEx(op, args @ _*) if op == TlaSetOper.in || op == TlaSetOper.notin =>
      // x \in S, x \notin S
      val a = varPool.fresh
      val opsig = OperT1(List(a, SetT1(a)), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*)
        if op == TlaSetOper.subseteq || op == TlaSetOper.subsetProper
          || op == TlaSetOper.supseteq || op == TlaSetOper.supsetProper =>
      // S \subseteq T, S \subset T, S \supseteq T, S \supset T
      val a = varPool.fresh
      val opsig = OperT1(List(SetT1(a), SetT1(a)), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.SUBSET, args @ _*) =>
      // SUBSET S
      val a = varPool.fresh
      val opsig = OperT1(List(SetT1(a)), SetT1(SetT1(a)))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.union, args @ _*) =>
      // UNION S
      val opsig = OperT1(List(SetT1(SetT1(VarT1("a")))), SetT1(VarT1("a")))
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*) if op == TlaSetOper.cap || op == TlaSetOper.cup || op == TlaSetOper.setminus =>
      // S \\intersect T, S \\union T, S \\ T
      val a = varPool.fresh
      val opsig = OperT1(List(SetT1(a), SetT1(a)), SetT1(a))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.times, args @ _*) =>
      // S \X T
      val typeVars = varPool.fresh(args.length)
      val opsig = OperT1(typeVars.map(SetT1(_)), SetT1(TupT1(typeVars :_*)))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.filter, bindingEx, bindingSet, pred) =>
      // { x \in S: P }
      // or, { <<x, ..., z>> \in S: P }
      // the principal type is (a => Bool) => Set(a)
      val bindings = translateBindings((bindingEx, bindingSet))
      val typeVars = varPool.fresh(bindings.length)

      // 1. When there is one argument, a set element has type "a", no tuple is involved.
      // 2. When there are multiple arguments,
      //    a set element has type type <<a, b>>, that is, it is a tuple
      val funFrom = if (bindings.length == 1) typeVars.head else TupT1(typeVars :_*)
      // the principal type is ((a, b) => Bool) => Set(<<a, b>>) or just (a => Bool) => Set(a)
      val principal = OperT1(Seq(OperT1(typeVars, BoolT1())), SetT1(funFrom))

      // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. P
      val lambda = mkAbs(BlameRef(ex.ID), this(pred), bindings :_*)
      // the resulting expression is ((((a, b) => Bool) => Set(<<a, b>>)) (λ x ∈ S, y ∈ T. P)
      mkApp(ExactRef(ex.ID), Seq(principal), lambda)

    case OperEx(TlaSetOper.map, mapExpr, args @ _*) =>
      // { x \in S, y \in T: e }
      val (vars, sets) = args.zipWithIndex.partition(_._2 % 2 == 0)
      if (vars.length != sets.length) {
        throw new TypingException("Invalid bound variables and sets in: " + ex)
      }
      val bindings = translateBindings(vars.map(_._1).zip(sets.map(_._1)) :_*)
      val a = varPool.fresh
      val otherTypeVars = varPool.fresh(bindings.length) // start with "b", as "a" goes to the result
      // the principal type of is ((b, c) => a) => Set(a)
      val principal = OperT1(Seq(OperT1(otherTypeVars, a)), SetT1(a))
      // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
      val lambda = mkAbs(BlameRef(mapExpr.ID), this(mapExpr), bindings: _*)
      mkApp(ExactRef(ex.ID), Seq(principal), lambda)

    //******************************************** FUNCTIONS **************************************************
    case OperEx(TlaFunOper.enum, args @ _*) =>
      // [f1 |-> e1, f2 |-> e2]
      val fields = args.zipWithIndex.collect {
        case (ValEx(TlaStr(name)), i) if i % 2 == 0 => name
        case (_, i) if i % 2 == 0 => throw new IllegalArgumentException("Expected ValEx(TlaStr(_)) as a field name")
      }
      val values = args.zipWithIndex.filter(_._2 % 2 == 1).map(p => this(p._1))
      val typeVars = fields.indices.map(_ => varPool.fresh)
      // (a, b) => [f1 |-> a, f2 |-> b]
      val sig = OperT1(typeVars, RecT1(fields.zip(typeVars) : _*))
      mkApp(ExactRef(ex.ID), Seq(sig), values: _*)

    case OperEx(TlaFunOper.tuple) =>
      // an empty sequence << >> is not an operator, but a polymorphic constant
      mkConst(ExactRef(ex.ID), SeqT1(VarT1("a")))

    case OperEx(TlaFunOper.tuple, args @ _*) =>
      // <<e_1, ..., e_n>>
      val typeVars = varPool.fresh(args.length)
      val a = if (typeVars.nonEmpty) typeVars.head else varPool.fresh
      val values = args.map(this(_))
      val tuple = OperT1(typeVars, TupT1(typeVars :_*))
      val as = List.fill(args.length)(a)
      val seq = OperT1(as, SeqT1(a))
      mkApp(ExactRef(ex.ID), Seq(tuple, seq), values: _*)

    case OperEx(TlaFunOper.app, fun, arg @ ValEx(TlaInt(fieldNo))) =>
      // f[i], where i is an integer literal
      val a = varPool.fresh
      val funType = OperT1(Seq(FunT1(IntT1(), a), IntT1()), a) // ((Int -> a), Int) => a
      val seqType = OperT1(Seq(SeqT1(a), IntT1()), a) // (Seq(a), Int) => a
      val tupType = OperT1(Seq(SparseTupT1(fieldNo.toInt -> a), IntT1()), a) // ({ 3: a }, Int) => a
      mkApp(ExactRef(ex.ID), Seq(funType, seqType, tupType), this(fun), mkConst(ExactRef(arg.ID), IntT1()))

    case OperEx(TlaFunOper.app, fun, arg @ ValEx(TlaStr(fieldName))) =>
      // f[s], where s is a string literal
      val a = varPool.fresh
      val funType = OperT1(Seq(FunT1(StrT1(), a), StrT1()), a) // ((Str -> a), Str) => a
      val recType = OperT1(Seq(RecT1(fieldName -> a), StrT1()), a) // ({ foo: a }, Str) => a
      mkApp(ExactRef(ex.ID), Seq(funType, recType), this(fun), mkConst(ExactRef(arg.ID), StrT1()))

    case OperEx(TlaFunOper.app, fun, arg) =>
      // the general case of f[e]
      val a = varPool.fresh
      val b = varPool.fresh
      val funType = OperT1(Seq(FunT1(a, b), a), b) // ((a -> b), a) => b
      val seqType = OperT1(Seq(SeqT1(a), IntT1()), a) // (Seq(a), Int) => a
      mkApp(ExactRef(ex.ID), Seq(funType, seqType), this(fun), this(arg))

    case OperEx(TlaFunOper.domain, fun) =>
      // DOMAIN f
      val a = varPool.fresh
      val b = varPool.fresh
      val funType = OperT1(Seq(FunT1(a, b)), SetT1(a)) // (a -> b) => Set(a)
      val seqType = OperT1(Seq(SeqT1(a)), SetT1(IntT1())) // Seq(a) => Set(Int)
      val recType = OperT1(Seq(RecT1()), SetT1(StrT1())) // [] => Set(Str)
      val tupType = OperT1(Seq(SparseTupT1()), SetT1(IntT1())) // {} => Set(Int)
      mkApp(ExactRef(ex.ID), Seq(funType, seqType, recType, tupType), this(fun))

    case OperEx(TlaFunOper.funDef, mapExpr, args @ _*) =>
      // [ x \in S, y \in T |-> e ]
      // or, [ <<x, y>> \in S, z \in T |-> e ]
      val (varEs, setEs) = args.zipWithIndex.partition(_._2 % 2 == 0)
      if (varEs.length != setEs.length) {
        throw new TypingException("Invalid bound variables and sets in: " + ex)
      }
      val bindings = translateBindings(varEs.map(_._1).zip(setEs.map(_._1)) :_*)
      val a = varPool.fresh
      val typeVars = varPool.fresh(bindings.length) // start with "b", as "a" goes to the result
      // 1. When there is one argument, the generated function has the type b -> a, that is, no tuple is involved.
      // 2. When there are multiple arguments,
      // the generated function has the type <<b, c>> -> a, that is, it accepts a tuple
      val funFrom = if (bindings.length == 1) typeVars.head else TupT1(typeVars :_*)
      // The principal type of is ((b, c) => a) => (<<b, c>> -> a).
      // Note that the generated function has the type <<b, c>> -> a, that is, it accepts a tuple.
      val principal = OperT1(Seq(OperT1(typeVars, a)),
        FunT1(funFrom, a))
      // the function definition implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
      val lambda = mkAbs(BlameRef(mapExpr.ID), this(mapExpr), bindings :_*)
      mkApp(ExactRef(ex.ID), Seq(principal), lambda)

    case OperEx(TlaFunOper.except, fun, args @ _*) =>
      // the hardest expression: [f EXCEPT ![e1] = e2, ![e3] = e4, ...]
      val accessors = args.zipWithIndex.filter(_._2 % 2 == 0) map { p => TlaFunOper.except.unpackIndex(p._1) }
      val newValues = args.zipWithIndex.filter(_._2 % 2 == 1) map { _._1 }
      assert(accessors.length == newValues.length)

      // if all accessors are string literals, then we are dealing with a record
      val allStrings = accessors.forall {
        case ValEx(TlaStr(_)) => true
        case _ => false
      }
      // if all accessors are integer literals, then we are dealing with a tuple, a sequence, or a function
      val allInts = accessors.forall {
        case ValEx(TlaInt(_)) => true
        case _ => false
      }

      // a function: ((a -> b), a, b) => (a -> b)
      // introduce a sequence of a, b, a, b, ... (as many as there are accessors)
      val a1 = varPool.fresh
      val b1 = varPool.fresh
      val aAndBs = List.fill(accessors.length)(List(a1, b1)).flatten
      val funType = OperT1(FunT1(a1, b1) +: aAndBs, FunT1(a1, b1))
      // a sequence: (Seq(a), Int, a, Int, a, ...) => Seq(a)
      val a2 = varPool.fresh
      val intAndAs = List.fill(accessors.length)(List(IntT1(), a2)).flatten
      val seqType = OperT1(SeqT1(a2) +: intAndAs, SeqT1(a2))
      // a record: ([foo: a, bar: b, ...], Str, a, Str, b, ...) => [foo: a, bar: b, ...]
      val typeVars = varPool.fresh(accessors.length) // introduce type variables a, b, c, ...
      val recFields = accessors.zip(typeVars).collect { case (ValEx(TlaStr(fieldName)), tv) => (fieldName, tv)}
      val rec = RecT1(recFields :_*)
      val strAndVars = typeVars.flatMap(v => List(StrT1(), v))
      val recType = OperT1(rec +: strAndVars, rec)
      // a tuple: ({3: a, 5: b, ...}, Int, a, Int, b, ...) => {3: a, 5: b, ...}
      val tupFields = accessors.zip(typeVars).collect { case (ValEx(TlaInt(fieldNo)), tv) => (fieldNo.toInt, tv)}
      val tup = SparseTupT1(tupFields :_*)
      val intAndVars = typeVars.flatMap(v => List(IntT1(), v))
      val tupType = OperT1(tup +: intAndVars, tup)

      // construct the disjunctive type
      val disjunctiveType =
        if (allStrings)
          Seq(funType, recType)
        else if (allInts)
          Seq(funType, seqType, tupType)
        else
          Seq(funType, seqType)

      // translate the arguments and interleave them
      val xargs = accessors.zip(newValues).flatMap(p => List(this (p._1), this (p._2)))
      mkApp(ExactRef(ex.ID), disjunctiveType, this(fun) +: xargs :_*)

    case OperEx(TlaFunOper.recFunDef, body, NameEx(name), bindingSet) =>
      // the expected type is: (((a -> b) => (a => b)) => (a -> b)) (λ $recFun ∈ Set(c -> d). λ x ∈ Int. x)
      val a = varPool.fresh
      val b = varPool.fresh
      val funType = FunT1(a, b)
      val aToB = OperT1(Seq(a), b)
      val principal = OperT1(Seq(OperT1(Seq(funType), aToB)), funType)
      val innerLambda = mkAbs(ExactRef(body.ID), this(body), (name, this(bindingSet)))
      val c = varPool.fresh
      val d = varPool.fresh
      val outerLambda = mkAbs(BlameRef(ex.ID), innerLambda,
        (TlaFunOper.recFunRef.uniqueName, mkConst(BlameRef(ex.ID), SetT1(FunT1(c, d)))))
      mkApp(ExactRef(ex.ID), Seq(principal), outerLambda)

    case OperEx(TlaFunOper.recFunRef) =>
      mkName(ExactRef(ex.ID), TlaFunOper.recFunRef.uniqueName)

    //******************************************** CONTROL **************************************************

    case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
      // IF e1 THEN e2 ELSE E2
      // (Bool, a, a) => a
      val a = varPool.fresh
      val opsig = OperT1(List(BoolT1(), a, a), a)
      mkApp(ex.ID, opsig, Seq(predEx, thenEx, elseEx))

    case OperEx(op, args @ _*) if op == TlaControlOper.caseNoOther || op == TlaControlOper.caseWithOther =>
      // CASE p1 -> e1 [] p2 -> e2
      // CASE p1 -> e1 [] p2 -> e2 OTHER e3
      val nargs = args.length
      val nargs2 = (args.length / 2) * 2 // the largest even number below nargs
      // Bool, a, Bool, a, ...
      val a = varPool.fresh
      val boolAndAs = 0.until(nargs2).map(i => if (i % 2 == 0) BoolT1() else a)
      val operArgs = if (nargs % 2 == 1) a +: boolAndAs  else boolAndAs
      val opsig = OperT1(operArgs, a)
      mkApp(ex.ID, opsig, args)

    //******************************************** FiniteSets ************************************************
    case OperEx(TlaFiniteSetOper.isFiniteSet, setEx) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SetT1(a)), BoolT1())  // Set(a) => Bool
      mkApp(ex.ID, opsig, Seq(setEx))

    case OperEx(TlaFiniteSetOper.cardinality, setEx) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SetT1(a)), IntT1())   // Set(a) => Int
      mkApp(ex.ID, opsig, Seq(setEx))

    //*************************************** ACTION OPERATORS ***********************************************
    case OperEx(TlaActionOper.prime, inner) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(a), a)       // a => a
      mkApp(ex.ID, opsig, Seq(inner))

    case OperEx(TlaActionOper.stutter, args @ _*) =>
      // Bool, a, b, c => Bool
      val opsig = OperT1(BoolT1() +: varPool.fresh(args.length - 1), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaActionOper.nostutter, args @ _*) =>
      // Bool, a, b, c => Bool
      val opsig = OperT1(BoolT1() +: varPool.fresh(args.length - 1), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaActionOper.enabled, inner) =>
      val opsig = OperT1(Seq(BoolT1()), BoolT1())       // Bool => Bool
      mkApp(ex.ID, opsig, Seq(inner))

    case OperEx(TlaActionOper.unchanged, args @ _*) =>
      val opsig = OperT1(varPool.fresh(args.length), BoolT1())       // a, b, c => Bool
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaActionOper.composition, a, b) =>
      val opsig = OperT1(Seq(BoolT1(), BoolT1()), BoolT1())       // (Bool, Bool) => Bool
      mkApp(ex.ID, opsig, Seq(a, b))

    //******************************************** Sequences *************************************************
    case OperEx(TlaSeqOper.head, s) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SeqT1(a)), a)       // Seq(a) => a
      mkApp(ex.ID, opsig, Seq(s))

    case OperEx(TlaSeqOper.tail, s) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SeqT1(a)), SeqT1(a))       // Seq(a) => Seq(a)
      mkApp(ex.ID, opsig, Seq(s))

    case OperEx(TlaSeqOper.append, args @ _*) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SeqT1(a), a), SeqT1(a))       // Seq(a), a => Seq(a)
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSeqOper.concat, s, t) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SeqT1(a), SeqT1(a)), SeqT1(a)) // Seq(a), Seq(a) => Seq(a)
      mkApp(ex.ID, opsig, Seq(s, t))

    case OperEx(TlaSeqOper.len, s) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SeqT1(a)), IntT1())                             // Seq(a) => Int
      mkApp(ex.ID, opsig, Seq(s))

    case OperEx(TlaSeqOper.subseq, args @ _*) =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(SeqT1(a), IntT1(), IntT1()), SeqT1(a)) // Seq(a), Int, Int => Seq(a)
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSeqOper.selectseq, args @ _*) =>
      val a = varPool.fresh
      val filter = OperT1(Seq(a), BoolT1())
      val opsig = OperT1(Seq(SeqT1(a), filter), SeqT1(a)) // Seq(a), (a => Bool) => Seq(a)
      mkApp(ex.ID, opsig, args)

    //******************************************** INTEGERS **************************************************
    case OperEx(TlaArithOper.uminus, args @ _*) =>
      // -x
      val opsig = OperT1(Seq(IntT1()), IntT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*)
        if op == TlaArithOper.plus || op == TlaArithOper.minus || op == TlaArithOper.mult
          || op == TlaArithOper.div || op == TlaArithOper.mod || op == TlaArithOper.exp =>
      // x + y, x - y, x * y, x \div y, x % y, x^y
      val opsig = OperT1(List(IntT1(), IntT1()), IntT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*)
        if op == TlaArithOper.lt || op == TlaArithOper.le || op == TlaArithOper.gt || op == TlaArithOper.ge =>
      // x < y, x <= y, x > y, x >= y
      val opsig = OperT1(List(IntT1(), IntT1()), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*) if op == TlaArithOper.sum || op == TlaArithOper.prod =>
      // SUM(e_1, ..., e_n) or PROD(e_1, ..., e_n)
      val nInts = List.fill(args.length)(IntT1())
      val opsig = OperT1(nInts, IntT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaArithOper.dotdot, args @ _*) =>
      // a..b
      val opsig = OperT1(List(IntT1(), IntT1()), SetT1(IntT1()))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaArithOper.realDiv, args @ _*) =>
      // a / b
      val opsig = OperT1(List(RealT1(), RealT1()), RealT1())
      mkApp(ex.ID, opsig, args)

    //***************************************** TEMPORAL *************************************************
    case OperEx(op, inner) if op == TlaTempOper.box || op == TlaTempOper.diamond =>
      val opsig = OperT1(Seq(BoolT1()), BoolT1())       // Bool => Bool
      mkApp(ex.ID, opsig, Seq(inner))

    case OperEx(op, lhs, rhs) if op == TlaTempOper.guarantees || op == TlaTempOper.leadsTo =>
      val opsig = OperT1(Seq(BoolT1(), BoolT1()), BoolT1())       // (Bool, Bool) => Bool
      mkApp(ex.ID, opsig, Seq(lhs, rhs))

    case OperEx(op, sub, act) if op == TlaTempOper.weakFairness || op == TlaTempOper.strongFairness =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(a, BoolT1()), BoolT1())       // (a, Bool) => Bool
      mkApp(ex.ID, opsig, Seq(sub, act))

    case OperEx(op, varName, act) if op == TlaTempOper.AA || op == TlaTempOper.EE =>
      val a = varPool.fresh
      val opsig = OperT1(Seq(a, BoolT1()), BoolT1())       // (a, Bool) => Bool
      mkApp(ex.ID, opsig, Seq(varName, act))

    //******************************************** MISC **************************************************
    case wte @ OperEx(TypingOper.withType, _*) =>
      throw new TypingInputException("Found a type annotation in an unexpected place: " + wte)

    case _ =>
      val a = varPool.fresh
      mkConst(ExactRef(ex.ID), a)
  }

  /**
    * Usually, one uses bindings like x \in S, y \in T in set comprehensions and function definitions.
    * However, TLA+ allows for advanced syntax in bindings, e.g., << x, y >> \in S, << u, << v, w >> >> \in T.
    * This method does a general translation for variable bindings
    *
    * @param bindings pairs of expressions, e.g., (NameEx("x"), NameEx("S"))
    * @return translated bindings, where all tuples have been unpacked
    */
  private def translateBindings(bindings: (TlaEx, TlaEx)*): Seq[(String, EtcExpr)] = {
    // project a set of dim-tuples on the ith element (starting with 0!)
    def project(id: UID, setEx: EtcExpr, dim: Int, index: Int): EtcExpr = {
      val typeVars = varPool.fresh(dim)
      // e.g., Set(<<a, b, c>>) => Set(b)
      val operType = OperT1(Seq(SetT1(TupT1(typeVars :_*))), SetT1(typeVars(index)))
      // (operType set)
      mkApp(BlameRef(id), Seq(operType), setEx)
    }

    def unpackOne(id: UID, target: TlaEx, set: EtcExpr): Seq[(String, EtcExpr)] = {
      target match {
          // simplest case: name is bound to set
        case NameEx(name) =>
          Seq((name, set))

          // advanced case: <<x, y, ..., z>> is bound to set
        case OperEx(TlaFunOper.tuple, args @ _*) =>
          args.zipWithIndex.flatMap { case (a, i) => unpackOne(id, a, project(id, set, args.length, i)) }

        case _ =>
          throw new TypingInputException(s"Unexpected binding $target \\in $set")
      }

    }

    // unpack x \in S, <<y, z>> \in T into x \in S, y \in project(T, 1), z \in project(T, 2)
    bindings.flatMap { case (target, set) => unpackOne(set.ID, target, this(set)) }
  }

  // Translate a sequence of formal parameters into type variables
  private def formalParamsToTypeVars(params: Seq[FormalParam]): Seq[(String, TlaType1)] = {
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

  private def mkApp(uid: UID, sig: OperT1, args: Seq[TlaEx]): EtcExpr = {
    mkApp(ExactRef(uid), Seq(sig), args.map(this(_)) :_*)
  }

  private def renameVars(tt: TlaType1): TlaType1 = {
    val shift = tt.usedNames.toSeq.map(i => i -> VarT1(i + nextVarNum))
    nextVarNum += shift.size
    Substitution(shift :_*)(tt)
  }
}

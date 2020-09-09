package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.SortedMap

/**
  * TlaExTranslator takes a TLA+ expression and produces an STCExpr.
  * The most interesting part of this translation is dealing with the built-in operators.
  * This translator is an extension of the ideas that appear in SignatureGenerator by Jure Kukovec.
  *
  * @see at.forsyte.apalache.tla.types.SignatureGenerator
  *
  * @author Igor Konnov
  */
class TlaExTranslator {
  def apply(ex: TlaEx): STCExpr = ex match {
    case NameEx(name) =>
      // x becomes x
      STCName(name)(ex.ID)

    //*********************************************** LITERALS **************************************************
    case ValEx(TlaInt(_)) =>
      // an integer literal becomes IntT1
      STCConst(IntT1())(ex.ID)

    case ValEx(TlaBool(_)) =>
      // a Boolean literal becomes BoolT1
      STCConst(BoolT1())(ex.ID)

    case ValEx(TlaStr(_)) =>
      // a string literal becomes StrT1
      STCConst(StrT1())(ex.ID)

    case ValEx(TlaReal()) =>
      // a real literal becomes RealT1
      STCConst(RealT1())(ex.ID)

    case ValEx(TlaIntSet) =>
      // the set of all integers is SetT1(IntT1)
      STCConst(SetT1(IntT1()))(ex.ID)

    case ValEx(TlaNatSet) =>
      // the set of all naturals is SetT1(IntT1)
      STCConst(SetT1(IntT1()))(ex.ID)

    case ValEx(TlaRealSet) =>
      // the set of all reals is SetT1(RealT1)
      STCConst(SetT1(RealT1()))(ex.ID)

    case ValEx(TlaBoolSet) =>
      // the set of all Booleans is SetT1(BoolT1)
      STCConst(SetT1(BoolT1()))(ex.ID)

    case ValEx(TlaStrSet) =>
      // the set of all strings is SetT1(StrT1)
      STCConst(SetT1(StrT1()))(ex.ID)

    //******************************************** GENERAL OPERATORS **************************************************
    case OperEx(op, args @ _*) if op == TlaOper.eq || op == TlaOper.ne =>
      // x = y, x /= y
      val opsig = OperT1(Seq(VarT1("a"), VarT1("a")), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaOper.apply, opName, args @ _*) =>
      // F(e_1, ..., e_n)
      mkAppByName(ex.ID, opName, args)

    case OperEx(TlaOper.chooseBounded, NameEx(bindingVar), bindingSet, pred) =>
      // CHOOSE x \in S: P
      // the principal type of CHOOSE is (a => Bool) => a
      val chooseType = OperT1(Seq(OperT1(Seq(VarT1("a")), BoolT1())), VarT1("a"))
      // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
      val chooseLambda = STCAbs(this(pred), (bindingVar, this(bindingSet)))(ex.ID)
      // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
      STCApp(STCConst(chooseType)(ex.ID), chooseLambda) (ex.ID)

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
      val quantType = OperT1(Seq(OperT1(Seq(VarT1("a")), BoolT1())), BoolT1())
      // \E and \A implicitly introduce a lambda abstraction: λ x ∈ S. P
      val lambda = STCAbs(this(pred), (bindingVar, this(bindingSet)))(ex.ID)
      // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
      STCApp(STCConst(quantType)(ex.ID), lambda) (ex.ID)

    //******************************************** SETS **************************************************
    case OperEx(TlaSetOper.enumSet, args @ _*) =>
      // { 1, 2, 3 }
      val a = VarT1("a")
      val as = List.fill(args.length)(a)
      mkApp(ex.ID, OperT1(as, SetT1(a)), args)

    case OperEx(TlaSetOper.funSet, args @ _*) =>
      // [S -> T]
      val a = VarT1("a")
      val b = VarT1("b")
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
      val typeVars = mkBoundVars(0, sets.length)
      val recSetType = SetT1(RecT1(SortedMap(fields.zip(typeVars) :_*)))
      val opType = OperT1(typeVars.map(SetT1(_)), recSetType)
      mkApp(ex.ID, opType, sets)

    case OperEx(TlaSetOper.seqSet, arg) =>
      // Seq(S)
      val a = VarT1("a")
      val sig = OperT1(Seq(SetT1(a)), SeqT1(a))
      mkApp(ex.ID, sig, Seq(arg))

    case OperEx(op, args @ _*) if op == TlaSetOper.in || op == TlaSetOper.notin =>
      // x \in S, x \notin S
      val opsig = OperT1(List(VarT1("a"), SetT1(VarT1("a"))), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*)
        if op == TlaSetOper.subseteq || op == TlaSetOper.subsetProper
          || op == TlaSetOper.supseteq || op == TlaSetOper.supsetProper =>
      // S \subseteq T, S \subset T, S \supseteq T, S \supset T
      val opsig = OperT1(List(SetT1(VarT1("a")), SetT1(VarT1("a"))), BoolT1())
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.SUBSET, args @ _*) =>
      // SUBSET S
      val opsig = OperT1(List(SetT1(VarT1("a"))), SetT1(SetT1(VarT1("a"))))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.union, args @ _*) =>
      // UNION S
      val opsig = OperT1(List(SetT1(SetT1(VarT1("a")))), SetT1(VarT1("a")))
      mkApp(ex.ID, opsig, args)

    case OperEx(op, args @ _*) if op == TlaSetOper.cap || op == TlaSetOper.cup || op == TlaSetOper.setminus =>
      // S \\intersect T, S \\union T, S \\ T
      val opsig = OperT1(List(SetT1(VarT1("a")), SetT1(VarT1("a"))), SetT1(VarT1("a")))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.times, args @ _*) =>
      // S \X T
      val typeVars = mkBoundVars(0, args.length)
      val opsig = OperT1(typeVars.map(SetT1(_)), SetT1(TupT1(typeVars :_*)))
      mkApp(ex.ID, opsig, args)

    case OperEx(TlaSetOper.filter, NameEx(bindingVar), bindingSet, pred) =>
      // { x \in S: P }
      // the principal type is (a => Bool) => Set(a)
      val principal = OperT1(Seq(OperT1(Seq(VarT1("a")), BoolT1())), SetT1(VarT1("a")))
      // { x \in S: P } implicitly introduces a lambda abstraction: λ x ∈ S. P
      val lambda = STCAbs(this(pred), (bindingVar, this(bindingSet)))(ex.ID)
      // the resulting expression is (((a => Bool) => Set(a)) (λ x ∈ S. P))
      STCApp(STCConst(principal)(ex.ID), lambda) (ex.ID)

    case OperEx(TlaSetOper.map, mapExpr, args @ _*) =>
      // { x \in S, y \in T: e }
      val boundVarNames = args.zipWithIndex.collect {
        case (NameEx(name), i) if i % 2 == 0 => name
        case (_, i) if i % 2 == 0 => throw new IllegalArgumentException("Expected NameEx(_) as a var name")
      }
      val sets = args.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
      val typeVars = mkBoundVars(1, sets.length) // start with "b", as "a" goes to the result
      // the principal type of is ((b, c) => a) => Set(a)
      val principal = OperT1(Seq(OperT1(typeVars, VarT1("a"))), SetT1(VarT1("a")))
      // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
      val lambda = STCAbs(this(mapExpr), boundVarNames.zip(sets).map(p => (p._1, this(p._2))) :_*)(mapExpr.ID)
      STCApp(STCConst(principal)(ex.ID), lambda) (ex.ID)

    //******************************************** FUNCTIONS **************************************************
    case OperEx(TlaFunOper.enum, args @ _*) =>
      // [f1 |-> e1, f2 |-> e2]
      val fields = args.zipWithIndex.collect {
        case (ValEx(TlaStr(name)), i) if i % 2 == 0 => name
        case (_, i) if i % 2 == 0 => throw new IllegalArgumentException("Expected ValEx(TlaStr(_)) as a field name")
      }
      val values = args.zipWithIndex.filter(_._2 % 2 == 1).map(p => this(p._1))
      assert(fields.length <= TlaExTranslator.QNAMES.length) // does anybody need more than 26 record fields?
      val typeVars = fields.indices
        .map(i => TlaExTranslator.QNAMES(i).toString)
        .map(l => VarT1(l))
      // (a, b) => [f1 |-> a, f2 |-> b]
      val sig = OperT1(typeVars, RecT1(SortedMap(fields.zip(typeVars) : _*)))
      STCApp(STCConst(sig)(ex.ID), values: _*) (ex.ID)

    case OperEx(TlaFunOper.tuple, args @ _*) =>
      // <<e_1, ..., e_n>>
      assert(args.length <= TlaExTranslator.QNAMES.length) // does anybody need more than 26 tuple fields?
      val typeVars = mkBoundVars(0, args.length)
      val values = args.map(this(_))
      val tuple = OperT1(typeVars, TupT1(typeVars :_*))
      val as = List.fill(args.length)(VarT1("a"))
      val seq = OperT1(as, SeqT1(VarT1("a")))
      STCApp(STCConst(tuple, seq)(ex.ID), values: _*) (ex.ID)

    case OperEx(TlaFunOper.app, fun, arg @ ValEx(TlaInt(fieldNo))) =>
      // f[i], where i is an integer literal
      val funType = OperT1(Seq(FunT1(IntT1(), VarT1("a")), IntT1()), VarT1("a")) // ((Int -> a), Int) => a
      val seqType = OperT1(Seq(SeqT1(VarT1("a")), IntT1()), VarT1("a")) // (Seq(a), Int) => a
      val tupType = OperT1(Seq(SparseTupT1(SortedMap(fieldNo.toInt -> VarT1("a"))), IntT1()), VarT1("a")) // ({ 3: a }, Int) => a
      STCApp(STCConst(funType, seqType, tupType)(ex.ID), this(fun), STCConst(IntT1()) (arg.ID)) (ex.ID)

    case OperEx(TlaFunOper.app, fun, arg @ ValEx(TlaStr(fieldName))) =>
      // f[s], where s is a string literal
      val funType = OperT1(Seq(FunT1(StrT1(), VarT1("a")), StrT1()), VarT1("a")) // ((Str -> a), Str) => a
      val recType = OperT1(Seq(RecT1(SortedMap(fieldName -> VarT1("a"))), StrT1()), VarT1("a")) // ({ foo: a }, Str) => a
      STCApp(STCConst(funType, recType)(ex.ID), this(fun), STCConst(StrT1()) (arg.ID)) (ex.ID)

    case OperEx(TlaFunOper.app, fun, arg) =>
      // the general case of f[e]
      val funType = OperT1(Seq(FunT1(VarT1("a"), VarT1("b")), VarT1("a")), VarT1("b")) // ((a -> b), a) => b
      val seqType = OperT1(Seq(SeqT1(VarT1("a")), IntT1()), VarT1("a")) // (Seq(a), Int) => a
      STCApp(STCConst(funType, seqType)(ex.ID), this(fun), this(arg)) (ex.ID)

    case OperEx(TlaFunOper.domain, fun) =>
      // DOMAIN f
      val funType = OperT1(Seq(FunT1(VarT1("a"), VarT1("b"))), SetT1(VarT1("a"))) // (a -> b) => Set(a)
      val seqType = OperT1(Seq(SeqT1(VarT1("a"))), SetT1(IntT1())) // Seq(a) => Set(Int)
      val recType = OperT1(Seq(RecT1(SortedMap.empty)), SetT1(StrT1())) // [] => Set(Str)
      val tupType = OperT1(Seq(SparseTupT1(SortedMap.empty)), SetT1(IntT1())) // {} => Set(Int)
      STCApp(STCConst(funType, seqType, recType, tupType)(ex.ID), this(fun)) (ex.ID)

    case OperEx(TlaFunOper.funDef, mapExpr, args @ _*) =>
      // [ x \in S, y \in T |-> e ]
      val boundVarNames = args.zipWithIndex.collect {
        case (NameEx(name), i) if i % 2 == 0 => name
        case (_, i) if i % 2 == 0 => throw new IllegalArgumentException("Expected NameEx(_) as a var name")
      }
      val sets = args.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
      val typeVars = mkBoundVars(1, sets.length) // start with "b", as "a" goes to the result
      // the principal type of is ((b, c) => a) => (<<b, c>> -> a)
      val principal = OperT1(Seq(OperT1(typeVars, VarT1("a"))),
        FunT1(TupT1(typeVars :_*), VarT1("a")))
      // the function definition implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
      val lambda = STCAbs(this(mapExpr), boundVarNames.zip(sets).map(p => (p._1, this(p._2))) :_*)(mapExpr.ID)
      STCApp(STCConst(principal)(ex.ID), lambda) (ex.ID)

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
      val aAndBs = List.fill(accessors.length)(List(VarT1("a"), VarT1("b"))).flatten
      val funType = OperT1(FunT1(VarT1("a"), VarT1("b")) +: aAndBs, FunT1(VarT1("a"), VarT1("b")))
      // a sequence: (Seq(a), Int, a, Int, a, ...) => Seq(a)
      val intAndAs = List.fill(accessors.length)(List(IntT1(), VarT1("a"))).flatten
      val seqType = OperT1(SeqT1(VarT1("a")) +: intAndAs, SeqT1(VarT1("a")))
      // a record: ([foo: a, bar: b, ...], Str, a, Str, b, ...) => [foo: a, bar: b, ...]
      val typeVars = mkBoundVars(0, accessors.length) // introduce type variables a, b, c, ...
      val recFields = accessors.zip(typeVars).collect { case (ValEx(TlaStr(fieldName)), tv) => (fieldName, tv)}
      val rec = RecT1(SortedMap(recFields :_*))
      val strAndVars = typeVars.flatMap(v => List(StrT1(), v))
      val recType = OperT1(rec +: strAndVars, rec)
      // a tuple: ({3: a, 5: b, ...}, Int, a, Int, b, ...) => {3: a, 5: b, ...}
      val tupFields = accessors.zip(typeVars).collect { case (ValEx(TlaInt(fieldNo)), tv) => (fieldNo.toInt, tv)}
      val tup = SparseTupT1(SortedMap(tupFields :_*))
      val intAndVars = typeVars.flatMap(v => List(IntT1(), v))
      val tupType = OperT1(tup +: intAndVars, tup)

      // construct the disjunctive type
      val disjunctiveType =
        if (allStrings)
          STCConst(funType, recType)(ex.ID)
        else if (allInts)
          STCConst(funType, seqType, tupType)(ex.ID)
        else
          STCConst(funType, seqType)(ex.ID)

      // translate the arguments and interleave them
      val xargs = accessors.zip(newValues).flatMap(p => List(this (p._1), this (p._2)))
      STCApp(disjunctiveType, this(fun) +: xargs :_*) (ex.ID)

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

    case _ =>
      STCConst(VarT1("a"))(ex.ID)
  }

  private def mkBoundVars(start: Int, size: Int): Seq[VarT1] = {
    assert(start >= 0 && start + size <= TlaExTranslator.QNAMES.length)
    TlaExTranslator.QNAMES.slice(start, start + size).map(l => VarT1(l))
  }

  private def mkApp(uid: UID, sig: OperT1, args: Seq[TlaEx]): STCExpr = {
    // TODO: Avoid using the same uid twice. Otherwise, we cannot easily map expressions to their types
    STCApp(STCConst(sig)(uid), args.map(this(_)) :_*)(uid)
  }

  private def mkAppByName(uid: UID, opName: TlaEx, args: Seq[TlaEx]): STCExpr = {
    // TODO: Avoid using the same uid twice. Otherwise, we cannot easily map expressions to their types
    STCApp(this(opName), args.map(this(_)) :_*)(uid)
  }
}

object TlaExTranslator {
  protected val QNAMES = List(
    "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
    "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z")
}
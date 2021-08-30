package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaBoolSet
import at.forsyte.apalache.tla.lir.values._

/**
 * The base class of expressions that are produced by the builder. These expressions are to be further translated
 * by the code that knows how to treat types. E.g., see TypedPredefs and UntypedPredefs.
 */
sealed trait BuilderEx {

  /**
   * Wrap the expression block with an alias, which can be used for type assignments.
   *
   * @param alias alias name
   * @return a new block that wraps this one
   */
  def ?(alias: String): BuilderAlias = {
    BuilderAlias(this, alias)
  }
}

/**
 * An alias of an expression that can be used to tag the expression with a type later.
 *
 * @param target the target block
 * @param alias  a name
 */
case class BuilderAlias(target: BuilderEx, alias: String) extends BuilderEx {
  override def ?(newAlias: String): BuilderAlias = {
    throw new BuilderError(s"Internal builder error: Trying to overwrite alias $alias with $newAlias")
  }
}

/**
 * A constructed expression that does not need any further processing from the builder.
 *
 * @param ex a constructed expression
 */
case class BuilderTlaExWrapper(ex: TlaEx) extends BuilderEx

/**
 * A value to be constructed.
 *
 * @param tlaValue a TLA+ value
 */
case class BuilderVal(tlaValue: TlaValue) extends BuilderEx

/**
 * A name to be constructed.
 *
 * @param name a string
 */
case class BuilderName(name: String) extends BuilderEx

/**
 * An operator application to be constructed.
 *
 * @param oper an operator type
 * @param args arguments to the operator
 */
case class BuilderOper(oper: TlaOper, args: BuilderEx*) extends BuilderEx

/**
 * A LET-IN definition.
 *
 * @param body      the expression in the IN ... part.
 * @param builtDefs the definitions in the LET ... part.
 */
case class BuilderLet(body: BuilderEx, builtDefs: TlaOperDecl*) extends BuilderEx

/**
 * The base class for declarations that are produced by the builder. They have to be futher translated by
 * type-aware code, e.g., in TypedPredefs and UntypedPredefs.
 */
sealed trait BuilderDecl {}

/**
 * A building block of an operator declaration.
 *
 * @param name         operator name
 * @param formalParams formal parameters
 * @param body         the definition body
 */
case class BuilderOperDecl(name: String, formalParams: List[OperParam], body: BuilderEx) extends BuilderDecl

/**
 * <p>A builder for TLA expressions. A singleton instance of this class is defined in *.lir.convenience.</p>
 *
 * <p>Contains methods for constructing various types of [[TlaEx]] expressions, guaranteeing
 * correct arity where the arity of the associated [[oper.TlaOper TlaOper]] is fixed.</p>
 *
 * @author jkukovec, konnov
 */
class Builder {

  /**
   * Construct a builder block from a complete TLA expression. This method is usually not needed, as we are
   * using implicit conversions. It is here for the case you want to avoid implicits.
   *
   * @param ex an expression that builder treats as a completely constructed expression
   * @return the expression that is wrapped with BuilderCompiledEx
   */
  def fromTlaEx(ex: TlaEx): BuilderTlaExWrapper = {
    BuilderTlaExWrapper(ex)
  }

  /** Names and values */
  def name(nameString: String): BuilderName = {
    BuilderName(nameString)
  }

  def bigInt(value: BigInt): BuilderVal = BuilderVal(TlaInt(value))

  def decimal(value: BigDecimal): BuilderVal = BuilderVal(TlaDecimal(value))

  def int(value: Int): BuilderVal = BuilderVal(TlaInt(value))

  def bool(value: Boolean): BuilderVal = BuilderVal(TlaBool(value))

  def str(value: String): BuilderVal = BuilderVal(TlaStr(value))

  /**
   * The set BOOLEAN.
   *
   * @return the value expression that corresponds to BOOLEAN.
   */
  def booleanSet(): BuilderVal = BuilderVal(TlaBoolSet)

  /**
   * The set Int of all integers.
   *
   * @return the value expression that corresponds to Int.
   */
  def intSet(): BuilderVal = BuilderVal(TlaIntSet)

  /**
   * The set Nat of all natural numbers.
   *
   * @return the value expression that corresponds to Nat.
   */
  def natSet(): BuilderVal = BuilderVal(TlaNatSet)

  /** Declarations */

  def declOp(name: String, body: BuilderEx, params: OperParam*): BuilderOperDecl = {
    BuilderOperDecl(name, params.toList, body)
  }

  def appDecl(decl: TlaOperDecl, args: BuilderEx*): BuilderOper = {
    if (args.length == decl.formalParams.length) {
      val nameEx = BuilderName(decl.name)
      BuilderOper(TlaOper.apply, (nameEx +: args): _*)
    } else {
      throw new IllegalArgumentException(
          "Operator %s of %d parameters is applied to %d arguments"
            .format(decl.name, decl.formalParams.length, args.length))
    }
  }

  /** TlaOper */
  def eql(lhs: BuilderEx, rhs: BuilderEx): BuilderOper = {
    BuilderOper(TlaOper.eq, lhs, rhs)
  }

  def neql(lhs: BuilderEx, rhs: BuilderEx): BuilderOper = {
    BuilderOper(TlaOper.ne, lhs, rhs)
  }

  def appOp(operEx: BuilderEx, args: BuilderEx*): BuilderEx = {
    BuilderOper(TlaOper.apply, operEx +: args: _*)
  }

  def choose(variable: BuilderEx, predicate: BuilderEx): BuilderEx =
    BuilderOper(TlaOper.chooseUnbounded, variable, predicate)

  def choose(variable: BuilderEx, set: BuilderEx, predicate: BuilderEx): BuilderEx = {
    BuilderOper(TlaOper.chooseBounded, variable, set, predicate)
  }

  /**
   * Decorate a TLA+ expression with a label (a TLA+2 feature), e.g.,
   * lab(a, b) :: e decorates e with the label "lab" whose arguments are "a" and "b".
   * This method needs a type tag for `name` and `args`. The type of the expression itself is inherited from ex.
   *
   * @param ex   a TLA+ expression to decorate
   * @param name label identifier
   * @param args label arguments (also identifiers)
   * @return OperEx(TlaOper.label, ex, name as ValEx(TlaStr(_)), args as ValEx(TlaStr(_)))
   */
  def label(ex: BuilderEx, name: String, args: String*): BuilderEx = {
    val nameAsVal = BuilderVal(TlaStr(name))
    val argsAsVals = args.map(s => BuilderVal(TlaStr(s)))
    BuilderOper(TlaOper.label, ex +: nameAsVal +: argsAsVals: _*)
  }

  /** TlaBoolOper */
  def and(args: BuilderEx*): BuilderEx = {
    BuilderOper(TlaBoolOper.and, args: _*)
  }

  def or(args: BuilderEx*): BuilderEx = {
    BuilderOper(TlaBoolOper.or, args: _*)
  }

  def not(pred: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.not, pred)
  }

  def impl(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.implies, lhs, rhs)
  }

  def equiv(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.equiv, lhs, rhs)
  }

  def forall(variable: BuilderEx, set: BuilderEx, predicate: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.forall, variable, set, predicate)
  }

  def forall(variable: BuilderEx, predicate: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.forallUnbounded, variable, predicate)
  }

  def exists(variable: BuilderEx, set: BuilderEx, predicate: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.exists, variable, set, predicate)
  }

  def exists(variable: BuilderEx, predicate: BuilderEx): BuilderEx = {
    BuilderOper(TlaBoolOper.existsUnbounded, variable, predicate)
  }

  /** TlaActionOper */
  def prime(name: BuilderEx): BuilderEx = {
    BuilderOper(TlaActionOper.prime, name)
  }

  def primeEq(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    eql(prime(lhs), rhs)
  }

  def stutt(action: BuilderEx, underscored: BuilderEx): BuilderEx = {
    BuilderOper(TlaActionOper.stutter, action, underscored)
  }

  def nostutt(action: BuilderEx, underscored: BuilderEx): BuilderEx = {
    BuilderOper(TlaActionOper.nostutter, action, underscored)
  }

  def enabled(action: BuilderEx): BuilderEx = {
    BuilderOper(TlaActionOper.enabled, action)
  }

  def unchanged(expr: BuilderEx): BuilderEx = {
    BuilderOper(TlaActionOper.unchanged, expr)
  }

  /** UNTESTED */
  def unchangedTup(args: BuilderEx*): BuilderEx = {
    unchanged(tuple(args: _*))
  }

  def comp(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaActionOper.composition, lhs, rhs)
  }

  /** TlaControlOper */
  def caseAny(guard1: BuilderEx, effect1: BuilderEx, guardsAndEffectsInterleaved: BuilderEx*): BuilderEx = {
    if (guardsAndEffectsInterleaved.size % 2 == 0) {
      caseSplit(guard1, effect1, guardsAndEffectsInterleaved: _*)
    } else {
      caseOther(guard1, effect1, guardsAndEffectsInterleaved.head, guardsAndEffectsInterleaved.tail: _*)
    }
  }

  def caseSplit(guard1: BuilderEx, effect1: BuilderEx, guardsAndEffectsInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaControlOper.caseNoOther, guard1 +: effect1 +: guardsAndEffectsInterleaved: _*)
  }

  def caseOther(effectOnOther: BuilderEx, guard1: BuilderEx, effect1: BuilderEx,
      guardsAndEffectsInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaControlOper.caseWithOther, effectOnOther +: guard1 +: effect1 +: guardsAndEffectsInterleaved: _*)
  }

  def ite(condition: BuilderEx, thenArm: BuilderEx, elseArm: BuilderEx): BuilderEx = {
    BuilderOper(TlaControlOper.ifThenElse, condition, thenArm, elseArm)
  }

  // [[LetIn]]
  def letIn(body: BuilderEx, defs: TlaOperDecl*): BuilderEx = {
    BuilderLet(body, defs: _*)
  }

  /** TlaTempOper */
  def AA(variable: BuilderEx, formula: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.AA, variable, formula)
  }

  def EE(variable: BuilderEx, formula: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.EE, variable, formula)
  }

  def box(formula: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.box, formula)
  }

  def diamond(formula: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.diamond, formula)
  }

  def guarantees(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.guarantees, lhs, rhs)
  }

  def leadsTo(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.leadsTo, lhs, rhs)
  }

  def SF(underscored: BuilderEx, action: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.strongFairness, underscored, action)
  }

  def WF(underscored: BuilderEx, action: BuilderEx): BuilderEx = {
    BuilderOper(TlaTempOper.weakFairness, underscored, action)
  }

  /** TlaArithOper */

  def plus(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.plus, lhs, rhs)
  }

  def minus(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.minus, lhs, rhs)
  }

  def uminus(arg: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.uminus, arg)
  }

  def mult(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.mult, lhs, rhs)
  }

  def div(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.div, lhs, rhs)
  }

  def mod(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.mod, lhs, rhs)
  }

  def rDiv(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.realDiv, lhs, rhs)
  }

  def exp(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.exp, lhs, rhs)
  }

  def dotdot(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.dotdot, lhs, rhs)
  }

  def lt(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.lt, lhs, rhs)
  }

  def gt(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.gt, lhs, rhs)
  }

  def le(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.le, lhs, rhs)
  }

  def ge(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlaArithOper.ge, lhs, rhs)
  }

  /** TlaFiniteSetOper */
  def card(set: BuilderEx): BuilderEx = {
    BuilderOper(TlaFiniteSetOper.cardinality, set)
  }

  def isFin(set: BuilderEx): BuilderEx = {
    BuilderOper(TlaFiniteSetOper.isFiniteSet, set)
  }

  /** TlaFunOper */
  def appFun(fun: BuilderEx, arg: BuilderEx): BuilderEx = {
    BuilderOper(TlaFunOper.app, fun, arg)
  }

  def dom(fun: BuilderEx): BuilderEx = {
    BuilderOper(TlaFunOper.domain, fun)
  }

  // TODO: rename to record, because it is used only for the records
  def enumFun(key1: BuilderEx, value1: BuilderEx, keysAndValuesInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaFunOper.enum, key1 +: value1 +: keysAndValuesInterleaved: _*)
  }

  def except(fun: BuilderEx, key1: BuilderEx, value1: BuilderEx, keysAndValuesInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaFunOper.except, fun +: key1 +: value1 +: keysAndValuesInterleaved: _*)
  }

  def funDef(mapExpr: BuilderEx, var1: BuilderEx, set1: BuilderEx, varsAndSetsInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaFunOper.funDef, mapExpr +: var1 +: set1 +: varsAndSetsInterleaved: _*)
  }

  def recFunDef(mapExpr: BuilderEx, var1: BuilderEx, set1: BuilderEx, varsAndSetsInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaFunOper.recFunDef, mapExpr +: var1 +: set1 +: varsAndSetsInterleaved: _*)
  }

  def recFunRef(): BuilderEx = {
    BuilderOper(TlaFunOper.recFunRef)
  }

  def tuple(args: BuilderEx*): BuilderEx = {
    BuilderOper(TlaFunOper.tuple, args: _*)
  }

  /** TlaSeqOper */
  def append(seq: BuilderEx, elem: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.append, seq, elem)
  }

  def concat(leftSeq: BuilderEx, rightSeq: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.concat, leftSeq, rightSeq)
  }

  def head(seq: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.head, seq)
  }

  def tail(seq: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.tail, seq)
  }

  def len(seq: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.len, seq)
  }

  /**
   * Get a subsequence of S, that is, SubSeq(S, from, to)
   *
   * @param seq       a sequence, e.g., constructed with tla.tuple
   * @param fromIndex the first index of the subsequene, greater or equal to 1
   * @param toIndex   the last index of the subsequence, not greater than Len(S)
   * @return the expression that corresponds to SubSeq(S, from, to)
   */
  def subseq(seq: BuilderEx, fromIndex: BuilderEx, toIndex: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.subseq, seq, fromIndex, toIndex)
  }

  /**
   * Get the subsequence of S that consists of the elements matching a predicate.
   *
   * @param seq  a sequence
   * @param test a predicate, it should be an action name
   * @return the expression that corresponds to SelectSeq(S, test)
   */
  def selectseq(seq: BuilderEx, test: BuilderEx): BuilderEx = {
    BuilderOper(TlaSeqOper.selectseq, seq, test)
  }

  /** TlaSetOper */
  def enumSet(args: BuilderEx*): BuilderEx = {
    BuilderOper(TlaSetOper.enumSet, args: _*)
  }

  def emptySet(): BuilderEx = {
    enumSet()
  }

  def in(elem: BuilderEx, set: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.in, elem, set)
  }

  def notin(elem: BuilderEx, set: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.notin, elem, set)
  }

  def cap(leftSet: BuilderEx, rightSet: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.cap, leftSet, rightSet)
  }

  def cup(leftSet: BuilderEx, rightSet: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.cup, leftSet, rightSet)
  }

  def union(set: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.union, set)
  }

  def filter(variable: BuilderEx, set: BuilderEx, predicate: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.filter, variable, set, predicate)
  }

  def map(mapExpr: BuilderEx, var1: BuilderEx, set1: BuilderEx, varsAndSetsInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaSetOper.map, mapExpr +: var1 +: set1 +: varsAndSetsInterleaved: _*)
  }

  def funSet(fromSet: BuilderEx, toSet: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.funSet, fromSet, toSet)
  }

  def recSet(varsAndSetsInterleaved: BuilderEx*): BuilderEx = {
    BuilderOper(TlaSetOper.recSet, varsAndSetsInterleaved: _*)
  }

  def seqSet(p_S: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.seqSet, p_S)
  }

  def subseteq(leftSet: BuilderEx, rightSet: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.subseteq, leftSet, rightSet)
  }

  def setminus(leftSet: BuilderEx, rightSet: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.setminus, leftSet, rightSet)
  }

  def times(sets: BuilderEx*): BuilderEx = {
    BuilderOper(TlaSetOper.times, sets: _*)
  }

  def powSet(set: BuilderEx): BuilderEx = {
    BuilderOper(TlaSetOper.powerset, set)
  }

  // tlc
  def tlcAssert(assertion: BuilderEx, errorMessage: String): BuilderEx = {
    BuilderOper(TlcOper.assert, assertion, BuilderVal(TlaStr(errorMessage)))
  }

  def primeInSingleton(nameToPrime: BuilderEx, onlySetElem: BuilderEx): BuilderEx = {
    in(prime(nameToPrime), enumSet(onlySetElem))
  }

  /**
   * The TLC operator that creates a singleton function: key :> value.
   */
  def colonGreater(key: BuilderEx, value: BuilderEx): BuilderEx = {
    BuilderOper(TlcOper.colonGreater, key, value)
  }

  /**
   * The TLC operator that concatenates two functions: fun1 @@ fun2.
   *
   * @param lhs function on the left-hand side
   * @param rhs function on the right-hand side
   * @return a new function that operates on the joint domain of lhs and rhs
   */
  def atat(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(TlcOper.atat, lhs, rhs)
  }

  /**
   * Produce a function out of a sequence of keys and values, that is, key_1 :> value_1 @@ ... @@ key_k :> value_k.
   *
   * TODO: this method introduces an intermediate builder expression, so it cannot be used to construct a typed expression.
   *
   * @param args an alternating list of keys and values
   */
  def atatInterleaved(args: BuilderEx*): BuilderEx = {
    if (args.isEmpty) {
      BuilderOper(TlcOper.atat)
    } else {
      val kvs = args.sliding(2, 2).toList
      val pairs = kvs.map(p => BuilderOper(TlcOper.colonGreater, p.head, p(1)))
      BuilderOper(TlcOper.atat, pairs: _*)
    }
  }

  def assign(lhs: BuilderEx, rhs: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.assign, lhs, rhs)
  }

  def assignPrime(leftName: BuilderEx, rightExpr: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.assign, prime(leftName), rightExpr)
  }

  def apalacheExpand(ex: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.expand, ex)
  }

  def apalacheSkolem(ex: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.skolem, ex)
  }

  def apalacheConstCard(ex: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.constCard, ex)
  }

  def apalacheFunAsSeq(funEx: BuilderEx, lenEx: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.funAsSeq, funEx, lenEx)
  }

  def apalacheGen(boundEx: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.gen, boundEx)
  }

  def apalacheDistinct(args: BuilderEx*): BuilderEx = {
    BuilderOper(ApalacheOper.distinct, args: _*)
  }

  def apalacheFoldSet(pairOp: BuilderEx, base: BuilderEx, set: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.foldSet, pairOp, base, set)
  }

  def apalacheFoldSeq(pairOp: BuilderEx, base: BuilderEx, seq: BuilderEx): BuilderEx = {
    BuilderOper(ApalacheOper.foldSeq, pairOp, base, seq)
  }

  private val m_nameMap: Map[String, TlaOper] =
    scala.collection.immutable.Map(
        TlaOper.eq.name -> TlaOper.eq,
        TlaOper.ne.name -> TlaOper.ne,
        TlaOper.apply.name -> TlaOper.apply,
        TlaOper.chooseBounded.name -> TlaOper.chooseBounded,
        TlaOper.chooseUnbounded.name -> TlaOper.chooseUnbounded,
        TlaBoolOper.and.name -> TlaBoolOper.and,
        TlaBoolOper.or.name -> TlaBoolOper.or,
        TlaBoolOper.not.name -> TlaBoolOper.not,
        TlaBoolOper.implies.name -> TlaBoolOper.implies,
        TlaBoolOper.equiv.name -> TlaBoolOper.equiv,
        TlaBoolOper.forall.name -> TlaBoolOper.forall,
        TlaBoolOper.exists.name -> TlaBoolOper.exists,
        TlaBoolOper.forallUnbounded.name -> TlaBoolOper.forallUnbounded,
        TlaBoolOper.existsUnbounded.name -> TlaBoolOper.existsUnbounded,
        TlaActionOper.prime.name -> TlaActionOper.prime,
        TlaActionOper.stutter.name -> TlaActionOper.stutter,
        TlaActionOper.nostutter.name -> TlaActionOper.nostutter,
        TlaActionOper.enabled.name -> TlaActionOper.enabled,
        TlaActionOper.unchanged.name -> TlaActionOper.unchanged,
        TlaActionOper.composition.name -> TlaActionOper.composition,
        TlaControlOper.caseNoOther.name -> TlaControlOper.caseNoOther,
        TlaControlOper.caseWithOther.name -> TlaControlOper.caseWithOther,
        TlaControlOper.ifThenElse.name -> TlaControlOper.ifThenElse,
        TlaTempOper.AA.name -> TlaTempOper.AA,
        TlaTempOper.box.name -> TlaTempOper.box,
        TlaTempOper.diamond.name -> TlaTempOper.diamond,
        TlaTempOper.EE.name -> TlaTempOper.EE,
        TlaTempOper.guarantees.name -> TlaTempOper.guarantees,
        TlaTempOper.leadsTo.name -> TlaTempOper.leadsTo,
        TlaTempOper.strongFairness.name -> TlaTempOper.strongFairness,
        TlaTempOper.weakFairness.name -> TlaTempOper.weakFairness,
        TlaArithOper.plus.name -> TlaArithOper.plus,
        TlaArithOper.uminus.name -> TlaArithOper.uminus,
        TlaArithOper.minus.name -> TlaArithOper.minus,
        TlaArithOper.mult.name -> TlaArithOper.mult,
        TlaArithOper.div.name -> TlaArithOper.div,
        TlaArithOper.mod.name -> TlaArithOper.mod,
        TlaArithOper.realDiv.name -> TlaArithOper.realDiv,
        TlaArithOper.exp.name -> TlaArithOper.exp,
        TlaArithOper.dotdot.name -> TlaArithOper.dotdot,
        TlaArithOper.lt.name -> TlaArithOper.lt,
        TlaArithOper.gt.name -> TlaArithOper.gt,
        TlaArithOper.le.name -> TlaArithOper.le,
        TlaArithOper.ge.name -> TlaArithOper.ge,
        TlaFiniteSetOper.cardinality.name -> TlaFiniteSetOper.cardinality,
        TlaFiniteSetOper.isFiniteSet.name -> TlaFiniteSetOper.isFiniteSet,
        TlaFunOper.app.name -> TlaFunOper.app,
        TlaFunOper.domain.name -> TlaFunOper.domain,
        TlaFunOper.enum.name -> TlaFunOper.enum,
        TlaFunOper.except.name -> TlaFunOper.except,
        TlaFunOper.funDef.name -> TlaFunOper.funDef,
        TlaFunOper.tuple.name -> TlaFunOper.tuple,
        TlaSeqOper.append.name -> TlaSeqOper.append,
        TlaSeqOper.concat.name -> TlaSeqOper.concat,
        TlaSeqOper.head.name -> TlaSeqOper.head,
        TlaSeqOper.tail.name -> TlaSeqOper.tail,
        TlaSeqOper.len.name -> TlaSeqOper.len,
        TlaSetOper.enumSet.name -> TlaSetOper.enumSet,
        TlaSetOper.in.name -> TlaSetOper.in,
        TlaSetOper.notin.name -> TlaSetOper.notin,
        TlaSetOper.cap.name -> TlaSetOper.cap,
        TlaSetOper.cup.name -> TlaSetOper.cup,
        TlaSetOper.filter.name -> TlaSetOper.filter,
        TlaSetOper.funSet.name -> TlaSetOper.funSet,
        TlaSetOper.map.name -> TlaSetOper.map,
        TlaSetOper.powerset.name -> TlaSetOper.powerset,
        TlaSetOper.recSet.name -> TlaSetOper.recSet,
        TlaSetOper.seqSet.name -> TlaSetOper.seqSet,
        TlaSetOper.setminus.name -> TlaSetOper.setminus,
        TlaSetOper.subseteq.name -> TlaSetOper.subseteq,
        TlaSetOper.times.name -> TlaSetOper.times,
        TlaSetOper.union.name -> TlaSetOper.union
    )

  def byName(operatorName: String, args: BuilderEx*): BuilderEx = {
    BuilderOper(m_nameMap(operatorName), args: _*)
  }

  def byNameOrNull(operatorName: String, args: BuilderEx*): BuilderEx =
    m_nameMap
      .get(operatorName)
      .map(op =>
        if (op.isCorrectArity(args.size))
          BuilderOper(op, args: _*)
        else BuilderTlaExWrapper(NullEx)
      )
      .getOrElse(BuilderTlaExWrapper(NullEx))
}

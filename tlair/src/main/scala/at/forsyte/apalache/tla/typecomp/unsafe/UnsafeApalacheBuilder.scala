package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
 * Scope-unsafe builder for ApalacheOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeApalacheBuilder extends ProtoBuilder with UnsafeLiteralAndNameBuilder {
  val strict: Boolean
  // We extend LiteralBuilder to make TLA integers from Scala ints

  /**
   * {{{lhs := rhs}}}
   * @param lhs
   *   must be a primed variable name.
   */
  def assign(lhs: TlaEx, rhs: TlaEx): TlaEx = {
    if (strict) require(lhs match {
          case OperEx(TlaActionOper.prime, _: NameEx) => true
          case _                                      => false
        }, s"Expected lhs to be a primed variable name, found $lhs.")
    buildBySignatureLookup(ApalacheOper.assign, lhs, rhs)
  }

  /**
   * {{{Gen(boundEx): returnType}}}
   *
   * Produce an Apalache generator for a bound expression and the return type. Can return any type of expression, so the
   * type must be manually provided, as it cannot be inferred from the argument.
   *
   * @param boundEx
   *   a bound expression, which must be constant after all simplifications
   */
  def gen(boundEx: TlaEx, returnType: TlaType1): TlaEx = {
    OperEx(ApalacheOper.gen, boundEx)(Typed(returnType))
  }

  /**
   * {{{Repeat(F, N, x): t}}}
   * @param n
   *   must be a nonnegative constant expression
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def repeat(F: TlaEx, n: BigInt, x: TlaEx): TlaEx = {
    if (strict) require(n > 0, s"Expected n to be positive, found $n.")
    if (strict) require(isNaryPassByName(n = 2)(F), s"Expected F to be a binary operator passed by name, found $F.")
    buildBySignatureLookup(ApalacheOper.repeat, F, int(n), x)
  }

  /**
   * {{{Skolem(ex)}}}
   * @param ex
   *   must be an expression of the shape {{{\E x \in S: P}}}
   */
  def skolem(ex: TlaEx): TlaEx = {
    if (strict) require(ex match {
          case OperEx(TlaBoolOper.exists, _, _, _) => true
          case _                                   => false
        }, s"Expected ex to be an existential quantification, found $ex.")
    buildBySignatureLookup(ApalacheOper.skolem, ex)
  }

  /** {{{Guess(S)}}} */
  def guess(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.guess, S)

  /**
   * {{{Expand(ex)}}}
   * @param ex
   *   must be either `SUBSET S` or `[A -> B]`
   */
  def expand(ex: TlaEx): TlaEx = {
    if (strict) require(ex match {
          case OperEx(TlaSetOper.powerset, _)  => true
          case OperEx(TlaSetOper.funSet, _, _) => true
          case _                               => false
        }, s"Expected ex to be a powerset or function set, found $ex.")
    buildBySignatureLookup(ApalacheOper.expand, ex)
  }

  /**
   * {{{ConstCard(ex)}}}
   * @param ex
   *   must be an expression of the shape {{{Cardinality(S) >= N}}}
   */
  def constCard(ex: TlaEx): TlaEx = {
    if (strict) require(ex match {
          case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, _), ValEx(_: TlaInt)) => true
          case _                                                                                  => false
        }, s"Expected ex to be a cardinality comparison, found $ex.")
    buildBySignatureLookup(ApalacheOper.constCard, ex)
  }

  private def isNaryPassByName(n: Int)(ex: TlaEx): Boolean = ex match {
    case LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)) => appName == operName && params.size == n
    case _                                                          => false
  }

  /**
   * {{{MkSeq(n, F)}}}
   * @param n
   *   must be nonnegative
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def mkSeq(n: BigInt, F: TlaEx): TlaEx = {
    if (strict) {
      require(n >= 0, s"Expected n to be nonnegative, found $n.")
      require(isNaryPassByName(n = 1)(F), s"Expected F to be a unary operator passed by name, found $F.")
    }
    buildBySignatureLookup(ApalacheOper.mkSeq, int(n), F)
  }

  /**
   * {{{MkSeq(n, F)}}}
   * @param n
   *   must be a nonnegative constant expression
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def mkSeqConst(n: TlaEx, F: TlaEx): TlaEx = {
    if (strict) require(isNaryPassByName(n = 1)(F), s"Expected F to be a unary operator passed by name, found $F.")
    buildBySignatureLookup(ApalacheOper.mkSeq, n, F)
  }

  /**
   * {{{FoldSet(F, v, S)}}}
   * @param F
   *   must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}}
   */
  def foldSet(F: TlaEx, v: TlaEx, S: TlaEx): TlaEx = {
    if (strict) require(isNaryPassByName(n = 2)(F), s"Expected F to be a binary operator passed by name, found $F.")
    buildBySignatureLookup(ApalacheOper.foldSet, F, v, S)
  }

  /**
   * {{{FoldSeq(F, v, seq)}}}
   * @param F
   *   must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}}
   */
  def foldSeq(F: TlaEx, v: TlaEx, seq: TlaEx): TlaEx = {
    if (strict) require(isNaryPassByName(n = 2)(F), s"Expected F to be a binary operator passed by name, found $F.")
    buildBySignatureLookup(ApalacheOper.foldSeq, F, v, seq)
  }

  /** {{{SetAsFun(S)}}} */
  def setAsFun(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.setAsFun, S)
}

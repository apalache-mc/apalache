package at.forsyte.apalache.tla.lir.oper

/**
 * The operators defined in the module Apalache.tla. This module gives the users a facility to provide hints.
 * The "Apalache" module is automatically looked up when Apalache is running.
 *
 * @author konnov
 */
abstract class ApalacheOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object ApalacheOper {

  /**
   * A type annotation of an expression with another expression that encodes a type.
   */
  @deprecated("This should not be used with the new type checker")
  object withType extends ApalacheOper {
    override def name: String = "Apalache!<:"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * An operator x <- e that is interpreted as an assignment of e to x (the variable can have a prime too).
   */
  object assign extends ApalacheOper {
    override def name: String = "Apalache!:="

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * A generator of a data structure. Given a positive integer `bound`, and assuming that the type of the operator
   * application is known, we recursively generate a TLA+ data structure as a tree, whose width is bound by the
   * number `bound`.
   */
  object gen extends ApalacheOper {
    override def name: String = "Apalache!Gen"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * Skolemization hint. In an expression Skolem(\E x \in S: e), the existential may be skolemized, that is, translated
   * into a constant.
   */
  object skolem extends ApalacheOper {
    override def name: String = "Apalache!Skolem"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * An expansion hint that can be applied to SUBSET S or [S -> T]. This hint orders the rewriter
   * to expand the underlying expression into a finite set. Since, such an expansion results in an exponential
   * blow up, this should be done carefully (and avoided as much as possible).
   */
  object expand extends ApalacheOper {
    override def name: String = "Apalache!Expand"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * An optimization hint for a cardinality constraint like Cardinality(S) >= k, where k is a constant.
   * Similar to BMC!Skolem, this optimization has to be applied carefully, as it is not sound, when the cardinality
   * test is located under negation.
   */
  object constCard extends ApalacheOper {
    override def name: String = "Apalache!ConstCardinality"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * The distinct operator that is equivalent to (distinct ...) in SMT-LIB.
   * Formally, BMC!Distinct(x_1, ..., x_n) is equivalent to \A i, j \in 1..n: i /= j => x_i /= x_j.
   *
   * XXX: there seems to be no way of defining a user-defined variadic operator in Apalache.tla.
   */
  object distinct extends ApalacheOper {
    override def name: String = "Apalache!Distinct"

    override def arity: OperArity = AnyArity()

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * Attempt to dynamically cast an Int -> T function to a Seq(T).
   * The first argument should be the function expression and the second argument
   * should be an integer, denoting the maximal length of the sequence.
   */
  object funAsSeq extends ApalacheOper {
    override def name: String = "Apalache!FunAsSeq"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * The FoldSet operator from the community modules. Given a binary
   * operator `Op(_,_)`, an initial value `v` and a set `S`, fold performs the
   * equivalent of S.foldLeft(v)(Op) in Scala, that is, iteratively applies Op to
   * the previous partial computation, starting with `v`, and an arbitrary element of S.
   *
   * The type signature is:
   * \forall T1,T2: FoldSet: ((T1,T2) => T1, T1, Set(T2)) => T
   *
   * The following equivalence should hold:
   * FoldSet( Op, v, S ) = IF S = {}
   *                       THEN v
   *                       ELSE LET w == CHOOSE x \in S: TRUE
   *                             IN LET T == S \ {w}
   *                                 IN FoldSet( Op, Op(v,w), T )
   */
  object foldSet extends ApalacheOper {
    override def name: String = "Apalache!FoldSet"

    override def arity: OperArity = FixedArity(3)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * The FoldSeq operator from the community modules. Similar to FoldSet, except the
   * evaluation order is determined by the sequence.
   *
   * The type signature is:
   * \forall T1,T2: FoldSeq: ((T1,T2) => T1, T1, Seq(T2)) => T
   *
   * The following equivalence should hold:
   * FoldSeq( Op, v, seq ) = IF seq = <<>>
   *                         THEN v
   *                         ELSE FoldSeq( Op, Op(v,Head(seq)), Tail(seq) )
   */
  object foldSeq extends ApalacheOper {
    override def name: String = "Apalache!FoldSeq"

    override def arity: OperArity = FixedArity(3)

    override val precedence: (Int, Int) = (100, 100)
  }
}

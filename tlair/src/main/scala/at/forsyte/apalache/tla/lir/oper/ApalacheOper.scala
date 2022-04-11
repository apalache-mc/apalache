package at.forsyte.apalache.tla.lir.oper

/**
 * The operators defined in the module Apalache.tla. This module gives the users a facility to provide hints. The
 * "Apalache" module is automatically looked up when Apalache is running.
 *
 * @author
 *   Igor Konnov, Rodrigo Otoni
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
   * application is known, we recursively generate a TLA+ data structure as a tree, whose width is bound by the number
   * `bound`.
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
   * Non-deterministically pick a value out of the set `S`, if `S` is non-empty. If `S` is empty, return some value of
   * the proper type. This can be understood as a non-deterministic version of `CHOOSE x \in S: TRUE`. Since we cannot
   * define a new syntactic form where `x` ranges over `S` in TLA+, we define the operator `Guess(S)` over a set `S`. If
   * you want to write a non-deterministic version of `CHOOSE x \in S: P`, simply write `Guess({ x \in S: P })`.
   */
  object guess extends TlaOper {
    /* the number of arguments the operator has */
    override val name: String = "Apalache!Guess"

    override def arity: OperArity = FixedArity(1)

    override def interpretation: Interpretation.Value = Interpretation.Predefined

    override val precedence: (Int, Int) = (0, 0) // see Section 15.2.1 in Lamport's book
  }

  /**
   * An expansion hint that can be applied to SUBSET S or [S -> T]. This hint orders the rewriter to expand the
   * underlying expression into a finite set. Since, such an expansion results in an exponential blow up, this should be
   * done carefully (and avoided as much as possible).
   */
  object expand extends ApalacheOper {
    override def name: String = "Apalache!Expand"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * An optimization hint for a cardinality constraint like Cardinality(S) >= k, where k is a constant. Similar to
   * BMC!Skolem, this optimization has to be applied carefully, as it is not sound, when the cardinality test is located
   * under negation.
   */
  object constCard extends ApalacheOper {
    override def name: String = "Apalache!ConstCardinality"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * The distinct operator that is equivalent to (distinct ...) in SMT-LIB. Formally, BMC!Distinct(x_1, ..., x_n) is
   * equivalent to \A i, j \in 1..n: i /= j => x_i /= x_j.
   *
   * XXX: there seems to be no way of defining a user-defined variadic operator in Apalache.tla.
   */
  object distinct extends ApalacheOper {
    override def name: String = "Apalache!Distinct"

    override def arity: OperArity = AnyArity()

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * <p>Attempt to dynamically cast an Int -> T function to a Seq(T). The first argument should be the function
   * expression and the second argument should be an integer, denoting the maximal length of the sequence.</p>
   *
   * <p>We keep this operator in the IR. However, we are using the definition of this operator from Apalache.tla. Hence,
   * if you construct an expression that contains `funAsSeq`, its constructor will throw.</p>
   */
  object funAsSeq extends ApalacheOper {
    require(false, "This operator is defined in Apalache.tla. Do not construct it.")

    override def name: String = "Apalache!FunAsSeq"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * A sequence constructor that is avoiding a function constructor. Since Apalache is typed, this operator is more
   * efficient than `FunAsSeq([ i \in 1..N |-> F(i) ])`.
   */
  object mkSeq extends ApalacheOper {
    override def name: String = "Apalache!MkSeq"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * The FoldSet operator from the community modules. Given a binary operator `Op(_,_)`, an initial value `v` and a set
   * `S`, fold performs the equivalent of S.foldLeft(v)(Op) in Scala, that is, iteratively applies Op to the previous
   * partial computation, starting with `v`, and an arbitrary element of S.
   *
   * The type signature is: \forall T1,T2: FoldSet: ((T1,T2) => T1, T1, Set(T2)) => T1
   *
   * The following equivalence should hold: FoldSet( Op, v, S ) = IF S = {} THEN v ELSE LET w == CHOOSE x \in S: TRUE IN
   * LET T == S \ {w} IN FoldSet( Op, Op(v,w), T )
   */
  object foldSet extends ApalacheOper {
    override def name: String = "Apalache!FoldSet"

    override def arity: OperArity = FixedArity(3)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * The FoldSeq operator from the community modules. Similar to FoldSet, except the evaluation order is determined by
   * the sequence.
   *
   * The type signature is: \forall T1,T2: FoldSeq: ((T1,T2) => T1, T1, Seq(T2)) => T1
   *
   * The following equivalence should hold: FoldSeq( Op, v, seq ) = IF seq = <<>> THEN v ELSE FoldSeq( Op,
   * Op(v,Head(seq)), Tail(seq) )
   */
  object foldSeq extends ApalacheOper {
    override def name: String = "Apalache!FoldSeq"

    override def arity: OperArity = FixedArity(3)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * <p>The operator SetAsFun converts a set of pairs `R` to a function `F`. The function `F` could be expressed as
   * follows:</p>
   *
   * <pre> LET Dom == { key: &lt;&lt;key, value&gt;&gt; \in R } Rng == { value: &lt;&lt;key, value&gt;&gt; \in R } IN [
   * key \in Dom |-> CHOOSE value \in Rng: &lt;&lt;key, value&gt;&gt; \in R ] </pre>
   *
   * <p>Note that the relation `R` may be ambiguous in the sense that the same key has more than one value. In this
   * case, the Apalache encodings choose one of the values, which corresponds to `CHOOSE`.</p>
   */
  object setAsFun extends ApalacheOper {
    override def name: String = "Apalache!SetAsFun"

    override def arity: OperArity = FixedArity(1)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * Wrapper for call-by-name expressions (values with operator types). Used to signify special treatment in
   * preprocessing passes.
   */
  object callByName extends ApalacheOper {
    override def name: String = "Apalache!CallByName"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (100, 100)
  }

  /**
   * The selectInSet operator is a variant of TlaSetOper.in. It signals that set membership should be checked.
   */
  object selectInSet extends ApalacheOper {
    override def name: String = "Apalache!SelectInSet"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The storeInSet operator is a variant of TlaSetOper.in when handling sets. It signals set membership. It is also
   * used to update functions, in which case the updated value is provided as an additional argument.
   */
  object storeInSet extends ApalacheOper {
    override def name: String = "Apalache!StoreInSet"

    override def arity: OperArity = FixedArity(2) || FixedArity(3)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The storeNotInSet operator is a variant of storeInSet. It signals that the negation of set membership should be
   * enforced.
   */
  object storeNotInSet extends ApalacheOper {
    override def name: String = "Apalache!UnchangedSet"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The smtMap operator applies an SMT map using conjunction to two cells encoded as SMT arrays. Its current use is to
   * encoded set intersection when handling TLA+ filters.
   */
  object smtMap extends ApalacheOper {
    override def name: String = "Apalache!SmtMap"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The unconstrainArray operator increases the SSA index of a cell encoded as an SMT array.
   */
  object unconstrainArray extends ApalacheOper {
    override def name: String = "Apalache!UnconstrainArray"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (5, 5)
  }
}

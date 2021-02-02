Type reconstruction API
=======================

**Author: Igor Konnov**

In this note, we focus on the client interface of a type inference engine for TLA+.
In the following, we refer to this interface as ``TI``.
By fixing this interface we give the users the freedom of choosing from several
type inference engines.

Given a TLA+ expression ``ex``, the ultimate goal of type inference is to assign a type
to each subexpression of ``ex`` in a sound and non-contradictory way. Since there may exist
many good type systems for TLA+, the type inference API _should_ be parameterized by the
base class of the type system. For instance, if a concrete type inference engine ``TIE`` is
implemented for the ``CellT`` type system, then ``TIE`` implements ``TI[CellT]``. Obviously,
a concrete implementation _may_ support one type system.

An implementation of ``TI`` _must_ support two main phases of operation:

1. **Type inference/reconstruction**. In this phase, ``TIE`` takes a TLA+ expression
  at its input, typically the body of ``Init`` or ``Next``, and it tries to find a type
  assignment to the variables, operator definitions, and operator usages. The challenges of
  this analysis are as follows:

   1. Resolving operator overloading, e.g., the expressions ``<<1, 2>>`` and ``f[e]``
    can be treated as expressions either over tuples, or sequences.

   1. Finding signatures for operator definitions, e.g., ``F(x) == x + 1`` should have
    the signature ``Int => Int``.

   If successful, the results of this analysis should be stored somewhere for the subsequent use
   in the _Type computation_ mode. Note that it is not necessary to store the types of all the intermediate
   subexpressions -- that would be wasteful. This analysis should store only the results that cannot
   be deterministically computed in the next phase such as resolved operator signatures and types of the variables.
   ``TIE`` _may_ use expression identifiers to save the type information in some storage.

1. **Type computation**. In this phase, the client queries ``TIE`` by giving a ``TLA+`` expression
    and the types of its arguments. ``TIE`` computes and returns the resulting type of the expression.
    For instance, given the expression ``F(e)`` and the type ``Int`` of ``e``, ``TIE`` finds the signature
    ``F: 'a -> 'a`` in its internal storage and returns the type ``Int``. Given the expression ``{x, y}``
    and the argument types ``x: Int`` and ``y: Int``, it can find the resulting type ``Set[Int]`` without
    referring to the storage. In other words, ``TIE`` provides the user with **one step** of type inference.
    If there are no ambiguities in the type computation or the ambiguities can be resolved by quering the storage,
    ``TIE`` _must_ return the resulting type. **Importantly**, ``TIE`` _must_ assume that it can be given expressions
    that have not been analyzed in the first stage. Such expressions may originate from the rewriting techniques
    used by the client. In this case, ``TIE`` _must_ try to compute the resulting type. Only if the resulting type
    cannot be deterministically computed (e.g., there is not relevant type information in the storage),
    should ``TIE`` fail.


## TIE Interface

```scala
/**
  * A diagnostic message.
  * @param origin the expression that caused the type error
  * @param explanation the explanation
  */
class TypeError(val origin: TlaEx, val explanation: String)

/**
  * A general interface to a type inference engine. Check the description in docs/types-api.md.
  *
  * @tparam T the base class of the type system
  * @see CellT
  * @author Igor Konnov
  */
trait TypeFinder[T] {
  /**
    * Given a TLA+ expression, reconstruct the types and store them in an internal storage.
    * If the expression is not well-typed, diagnostic messages can be accessed with getTypeErrors.
    *
    * @param e a TLA+ expression.
    * @return true, if type inference was successful.
    */
  def inferAndSave(e: TlaEx): Boolean

  /**
    * Retrieve the type errors from the latest call to inferAndSave.
    * @return a list of type errors
    */
  val getTypeErrors: Seq[TypeError]

  /**
    * Given a TLA+ expression and the types of its arguments, compute the resulting type, if possible.
    * @param e a TLA+ expression
    * @param argTypes the types of the arguments.
    * @return the resulting type, if it can be computed
    * @throws TypeException, if the type cannot be computed.
    */
  def compute(e: TlaEx, argTypes: Seq[T]): T
}
```








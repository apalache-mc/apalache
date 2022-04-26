package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx}

/**
 * ReplacedFixed generates syntax-based substitution transformations, which replace every instance of one syntactic
 * form, which satisfies a TlaEx predicate, with a fresh copy of another.
 *
 * If a TlaEx `e` is passed, instead of a predicate, it defines the predicate to be syntactic equality with `e`.
 *
 * Example: `whenEqualsTo(NameEx("x"), NameEx("t_3"))` applied to `x + x` returns `t_3 + t_3`, but both instances of
 * `t_3` have distinct UIDs.
 *
 * The order of testing and recursion is as follows: In the case that both a parent and child node (resp.
 * ancestor/descendant) in the internal representation tree satisfy the testing predicate, the replacement will first
 * transform the child node(s), before testing the predicate on the, now modified, alternate parent node. Alternatively,
 * a node may not have satisfied the predicate initially, but does so after its child nodes have been transformed. In
 * this case, the transformation is also applied to the parent node, which satisfies the predicate after partial
 * transformation.
 *
 * Example:
 *
 * {{{
 * def replacementPredicate( ex: TlaEx ): Boolean = ex match {
 *   case OperEx(TlaArithOper.plus, NameEx("x"), NameEx("x")) => true
 *   case _ => false
 * }
 * val ex = OperEx(TlaArithOper.plus, NameEx("x"), OperEx(TlaArithOper.plus, NameEx("x"), NameEx("x")))
 *
 * val newEx = NameEx("x")
 *
 * whenMatches(replacementPredicate, newEx)(ex) == NameEx("x")
 * whenMatches(replacementPredicate, newEx)(ex) !=
 *   OperEx(TlaArithOper.plus, NameEx("x"), OperEx(TlaArithOper.plus, NameEx("x"), NameEx("x")))
 * }}}
 */
class ReplaceFixed(tracker: TransformationTracker) {

  /**
   * Returns a transformation which replaces an expression that is equal to `replacedEx` with an instance of `newEx`.
   *
   * @param patternEx
   *   if an expression equals to `patternEx`, it should be replaced
   * @param mkNewEx
   *   a function that produces a new unique expression to replace an expression that matches `replacementPredicate`
   */
  def whenEqualsTo(
      patternEx: TlaEx,
      mkNewEx: => TlaEx): TlaExTransformation = {
    whenMatches(ReplaceFixed.standardTests.isEqualTo(patternEx), mkNewEx)
  }

  /**
   * Returns a transformation which replaces every instance satisfying `replacementPredicate` with an expression
   * produced with `mkNewEx`.
   *
   * @param replacementPredicate
   *   if `replacementPredicate(ex)` holds true, then `ex` should be replaced
   * @param mkNewEx
   *   a function that produces a new unique expression to replace an expression that matches `replacementPredicate`
   */
  def whenMatches(
      replacementPredicate: TlaEx => Boolean,
      mkNewEx: => TlaEx, // takes a [=> TlaEx] to allow for the creation of new instances (with distinct UIDs)
    ): TlaExTransformation = tracker.trackEx { ex =>
    val partialFun: PartialFunction[TlaEx, TlaEx] = {
      case e if replacementPredicate(e) => mkNewEx
    }
    withFun(partialFun)(ex)
  }

  /**
   * Returns a transformation which replaces every expression that matches `partialFun`. The new expression is the
   * result that is returned by `partialFun`.
   *
   * @param partialFun
   *   if this partial function is applicable to an expression, replace the expression with the result returned by
   *   `partialFun`
   */
  def withFun(partialFun: PartialFunction[TlaEx, TlaEx]): TlaExTransformation = tracker.trackEx { ex =>
    // apply the partial function, if it's applicable; otherwise return the expression itself
    def tr(ex: TlaEx): TlaEx = {
      partialFun.lift(ex).getOrElse(ex)
    }

    lazy val self = withFun(partialFun)
    ex match {
      case LetInEx(body, defs @ _*) =>
        // Transform bodies of all op.defs
        val newDefs = defs.map(tracker.trackOperDecl { d => d.copy(body = self(d.body)) })
        val newBody = self(body)
        val retEx = if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
        tr(retEx)

      case OperEx(op, args @ _*) =>
        val newArgs = args.map(self)
        val retEx = if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)
        tr(retEx)

      case _ => tr(ex)
    }
  }
}

object ReplaceFixed {
  // Some examples of testing functions, which can be used as replacement criteria
  object standardTests {
    def isEqualTo(ex: TlaEx): TlaEx => Boolean = { otherEx =>
      ex == otherEx
    }
    def isNotEqualTo(ex: TlaEx): TlaEx => Boolean = { otherEx =>
      ex != otherEx
    }
    def hasLowerUID(higherUIDEx: TlaEx): TlaEx => Boolean = { lowerUIDEx =>
      lowerUIDEx.ID.id < higherUIDEx.ID.id
    }
    def hasHigherUID(lowerUIDEx: TlaEx): TlaEx => Boolean = { higherUIDEx =>
      lowerUIDEx.ID.id < higherUIDEx.ID.id
    }
  }

  def apply(tracker: TransformationTracker): ReplaceFixed = new ReplaceFixed(tracker)
}

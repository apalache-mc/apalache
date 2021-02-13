package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * ReplacedFixed generates syntax-based substitution transformations, which replace every instance
 * of one syntactic form, which satisfies a TlaEx predicate, with a fresh copy of another.
 *
 * If a TlaEx `e` is passed, instead of a predicate, it defines the predicate
 * to be syntactic equality with `e`.
 *
 * Example: ReplaceFixed( NameEx("x"), NameEx("t_3"), ... ) applied to x + x
 * returns t_3 + t_3, but both instances of t_3 have distinct UIDs.
 *
 * The order of testing and recursion is as follows:
 * In the case that both a parent and child node (resp. ancestor/descendant) in the internal representation
 * tree satisfy the testing predicate, the replacement will first transform the child node(s), before
 * testing the predicate on the, now modified, alternate parent node.
 * Alternatively, a node may not have satisfied the predicate initially, but does so after its child nodes
 * have been transformed. In this case, the transformation is also applied to the parent node, which
 * satisfies the predicate after partial transformation.
 *
 * Example:
 *
 * def replacementPredicate( ex: TlaEx ): Boolean = ex match {
 *     case OperEx(TlaArithOper.plus, NameEx("x"), NameEx("x")) => true
 *     case _ => false
 *     }
 * val ex = OperEx(TlaArithOper.plus, NameEx("x"), OperEx(TlaArithOper.plus, NameEx("x"), NameEx("x")) )
 *
 * val newEx = NameEx("x")
 *
 * apply( replacementPredicate, newEx )(ex) == NameEx("x")
 * apply( replacementPredicate, newEx )(ex) !=
 *    OperEx(TlaArithOper.plus, NameEx("x"), OperEx(TlaArithOper.plus, NameEx("x"), NameEx("x")) )
 */
class ReplaceFixed(tracker: TransformationTracker) {

  /** This method is applied to leaves in the expression tree */
  private def replaceOne(
      replacementPredicate: TlaEx => Boolean,
      newEx: => TlaEx // takes a [=> TlaEx] to allow for the creation of new instances (with distinct UIDs)
  ): TlaExTransformation = tracker.trackEx { ex =>
    if (replacementPredicate(ex)) newEx else ex
  }

  /**
   * Returns a transformation which replaces every instance satisfying `replacementPredicate`
   * with an instance of `newEx`
   */
  def apply(
      replacementPredicate: TlaEx => Boolean,
      newEx: => TlaEx // takes a [=> TlaEx] to allow for the creation of new instances (with distinct UIDs)
  ): TlaExTransformation = tracker.trackEx { ex =>
    val tr = replaceOne(replacementPredicate, newEx)
    lazy val self = apply(replacementPredicate, newEx)
    ex match {
      case LetInEx(body, defs @ _*) =>
        // Transform bodies of all op.defs
        val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = self(d.body)) }
        val newBody = self(body)
        val retEx = if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)
        tr(retEx)

      case OperEx(op, args @ _*) =>
        val newArgs = args map self
        val retEx = if (args == newArgs) ex else OperEx(op, newArgs: _*)
        tr(retEx)

      case _ => tr(ex)
    }
  }

  /** Convenience overload, for replacing with equality as the replacement predicate */
  def apply(
      replacedEx: TlaEx, newEx: => TlaEx
  ): TlaExTransformation =
    apply(ReplaceFixed.standardTests.isEqualTo(replacedEx), newEx)

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

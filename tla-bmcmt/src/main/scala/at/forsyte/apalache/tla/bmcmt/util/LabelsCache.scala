package at.forsyte.apalache.tla.bmcmt.util

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * An enumeration of kinds of labels that can be attached to expressions.
 */
sealed abstract class ExprToLabelKind {}

/**
 * A label that marks an expression as belonging to a certain initial transition.
 * @param index
 *   transition index
 */
case class InitTransKind(index: Integer) extends ExprToLabelKind {}

/**
 * A label that marks an expression as belonging to a certain next transition.
 * @param index
 *   transition index
 */
case class NextTransKind(index: Integer) extends ExprToLabelKind {}

/**
 * A label that marks an expression as belonging to a certain state invariant.
 * @param index
 *   invariant index
 */
case class VCKind(index: Integer) extends ExprToLabelKind {}

/**
 * A cache for labels that are attached to expressions. The cache is used to avoid repeated calls of
 * `TlaExUtil.findLabels`. When the same transition is evaluated multiple times, e.g., in the randomized simulator, it
 * seems unnecessary to recompute the labels on each call. Hence, this cache. We have not profiled this cache yet. It
 * may give us negligible speedup.
 */
class LabelsCache {
  private var labels = Map[ExprToLabelKind, Seq[String]]()

  /**
   * Get the labels of a certain kind that are attached to an expression. The result is cached.
   * @param kind
   *   the kind of labels to look for (and cache)
   * @param expr
   *   the expression to search for labels
   * @return
   *   the sequence of labels of the given kind that are attached to the expression
   */
  def getLabels(kind: ExprToLabelKind, expr: TlaEx): Seq[String] = {
    labels.get(kind) match {
      case Some(ls) => ls
      case None     =>
        val ls = TlaExUtil.findLabels(expr)
        labels = labels + (kind -> ls)
        ls
    }
  }
}

package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGrade, ExprGradeStore}
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * Cache rewriting results for the expressions of the grade Constant, State, and ActionFree.
  *
  * @author Igor Konnov
  */
class ExprCache(val store: ExprGradeStore) extends SimpleCache[TlaEx, (TlaEx, ExprGrade.Value)] {
  def put(key: TlaEx, value: TlaEx): Unit = {
    store.get(key.ID) match {
      case Some(g) => put(key, (value, g))
      case None => ()
    }
  }

  /**
    * Put a value into the cache.
    *
    * @param key   a key
    * @param valueAndGrade a value and a grade, which is ignored
    */
  override def put(key: TlaEx, valueAndGrade: (TlaEx, ExprGrade.Value)): Unit = {
    valueAndGrade._2 match {
      case ExprGrade.Constant | ExprGrade.StateFree | ExprGrade.ActionFree =>
        super.put(key, valueAndGrade)

      case _ =>
        () // ignore
    }
  }

  /**
    * Leave only constants in the cache.
    */
  def disposeActionLevel(): Unit = {
    def isConst(mapEntry: (TlaEx, ((TlaEx, ExprGrade.Value), Int))): Boolean =
      mapEntry._2._1._2 == ExprGrade.Constant

    cache = cache filter isConst
  }
}

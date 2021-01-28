package at.forsyte.apalache.tla.bmcmt.util

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

// TODO: this should probably go to tlair
object TlaExUtil {
  /**
    * Find the names that are used in an expression.
    * @param expr an expression
    * @return the set of used names
    */
  def findUsedNames(expr: TlaEx): Set[String] = {
    var used = Set[String]()

    def rec: TlaEx => Unit = {
      case NameEx(name) => used = used + name
      case OperEx(TlaActionOper.prime, NameEx(name)) => used = used + (name + "'")
      case OperEx(_, args @_*) => args foreach rec
      case _ => ()
    }

    rec(expr)
    used
  }
}

package at.forsyte.apalache.tla.bmcmt.util

import at.forsyte.apalache.tla.bmcmt.InvalidTlaExException
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx, TlaOperDecl}

object TlaExUtil {
  /**
    * Find the names that are used in an expression.
    * @param expr an expression
    * @return the set of used names
    */
  def findUsedNames(expr: TlaEx): Set[String] = {
    var used = Set[String]()

    def findRec: TlaEx => Unit = {
      case NameEx(name) =>
        used = used + name

      case OperEx(TlaActionOper.prime, NameEx(name)) =>
        used = used + (name + "'")

      case OperEx(_, args @_*) =>
        args foreach findRec

      case ex @ LetInEx(body, defs@_*) =>
        def findInDef: TlaOperDecl => Unit = {
          case TlaOperDecl(_, List(), body) =>
            findRec(body)

          case TlaOperDecl(name, params, _) =>
            val msg = "Operator %s: expected 0 parameters, found %d parameters".format(name, params.length)
            throw new InvalidTlaExException(msg, ex)
        }
        defs.foreach(findInDef)
        findRec(body)

      case _ => ()
    }

    findRec(expr)
    used
  }
}

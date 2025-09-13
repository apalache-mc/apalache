package at.forsyte.apalache.tla.bmcmt.util

import at.forsyte.apalache.tla.bmcmt.InvalidTlaExException
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx, TlaOperDecl, ValEx}

object TlaExUtil {
  private def isFold(op: TlaOper): Boolean = {
    op == ApalacheOper.foldSet || op == ApalacheOper.foldSeq
  }

  /**
   * Find the names that are used in an expression.
   *
   * @param expr
   *   an expression
   * @return
   *   the set of used names
   */
  def findUsedNames(expr: TlaEx): Set[String] = {
    var used = Set[String]()

    def findRec: TlaEx => Unit = {
      case NameEx(name) =>
        used = used + name

      case OperEx(TlaActionOper.prime, NameEx(name)) =>
        used = used + (name + "'")

      // ignore the names in the auxiliary let-in definition
      case OperEx(op, LetInEx(_, TlaOperDecl(_, _, localBody)), baseExAndCollectionEx @ _*) if isFold(op) =>
        findRec(localBody)
        baseExAndCollectionEx.foreach(findRec)

      // ignore the names in the auxiliary let-in definition
      case OperEx(ApalacheOper.repeat, LetInEx(_, TlaOperDecl(_, _, localBody)), boundAndBaseEx @ _*) =>
        findRec(localBody)
        boundAndBaseEx.foreach(findRec)

      // ignore the names in the auxiliary let-in definition
      case OperEx(ApalacheOper.mkSeq, len, LetInEx(_, TlaOperDecl(_, _, localBody))) =>
        findRec(localBody)
        findRec(len)

      case OperEx(_, args @ _*) =>
        args.foreach(findRec)

      case ex @ LetInEx(body, defs @ _*) =>
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

  /**
   * Find the labels that are used in an expression. We assume that the label names are unique. Hence, they are returned
   * as a sequence, not a set.
   *
   * @return
   *   the set of used labels
   */
  def findLabels: TlaEx => Seq[String] = {
    case OperEx(TlaOper.label, body, ValEx(TlaStr(name)), _*) =>
      name +: findLabels(body)

    case OperEx(_, args @ _*) =>
      args.flatMap(findLabels)

    case LetInEx(body, defs @ _*) =>
      defs.flatMap(d => findLabels(d.body)) ++ findLabels(body)

    case _ => Seq()
  }
}

package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * Replaces primitive-valued constants initialized in ConstInit
 * with the values they hold.
 */
class TlaConstInliner(tracker: TransformationTracker, constants: Set[String]) {

  type valMap = Map[String, ValEx]

  // Extracts the constants from the ConstInit body into a map
  def buildConstMap(initial: valMap)(ex: TlaEx): valMap = ex match {
    // We only inline primitive values, since ConstInit _may_ be arbitrarily complex
    case OperEx(TlaOper.eq, NameEx(c), v: ValEx) if constants.contains(c) =>
      initial.get(c) match {
        case None => initial + (c -> v)
        case Some(mapVal) =>
          if (mapVal != v)
            throw new TlaInputError(s"Constant $c has multiple initializations: $v and $mapVal.")
          else
            initial
      }
    case OperEx(_, args @ _*) =>
      args.foldLeft(initial) { case (m, arg) =>
        buildConstMap(m)(arg)
      }

    case LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val postDeclMap = defs.foldLeft(initial) { case (m, d) => buildConstMap(m)(d.body) }
      buildConstMap(postDeclMap)(body)
    case _ =>
      initial
  }

  def replaceConstWithValue(constValMap: valMap): TlaExTransformation = tracker.trackEx {
    case ex @ NameEx(c) if constants.contains(c) =>
      constValMap.get(c) match {
        case None    => ex
        case Some(v) => ValEx(v.value)(v.typeTag)
      }
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map replaceConstWithValue(constValMap)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      val tr = replaceConstWithValue(constValMap)
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = tr(d.body)) }
      val newBody = tr(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
    case ex => ex
  }

}

object TlaConstInliner {
  def apply(tracker: TransformationTracker, constants: Set[String]): TlaConstInliner =
    new TlaConstInliner(tracker, constants)
}

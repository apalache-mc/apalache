package at.forsyte.apalache.tla.lir

import _root_.at.forsyte.apalache.tla.lir.oper.TlaActionOper
import _root_.at.forsyte.apalache.tla.lir.oper.TlaTempOper

class TlaLevelFinder(module: TlaModule) {
  private val consts = Set(module.constDeclarations.map(_.name): _*)
  private val vars = Set(module.varDeclarations.map(_.name): _*)
  private val defs = Map(module.operDeclarations.map { d => d.name -> d }: _*)
  private var levelCacheMap: Map[String, TlaLevel] = Map()

  def getLevelOfName(callers: Set[String], name: String): TlaLevel = {
    if (consts.contains(name)) {
      TlaLevelConst
    } else if (vars.contains(name)) {
      TlaLevelState
    } else {
      if (!callers.contains(name) && defs.contains(name)) {
        // as the module comes from the parser, we assume that defs contains a definition for the name `name`
        levelCacheMap.get(name) match {
          case Some(level) => level

          case None =>
            val level = getLevelOfExpression(callers + name, defs(name).body)
            levelCacheMap += name -> level
            level
        }
      } else {
        TlaLevelConst
      }
    }
  }

  def getLevelOfExpression(callers: Set[String], ex: TlaEx): TlaLevel = {
    ex match {
      case NameEx(name) =>
        getLevelOfName(callers, name)

      case OperEx(op, args @ _*) =>
        val level = TlaLevelFinder.levelOfOper.getOrElse(op, TlaLevelConst)
        level.join(args.map(getLevelOfExpression(callers, _: TlaEx)))

      case LetInEx(body, defs @ _*) =>
        getLevelOfExpression(callers, body).join(defs.map(d => getLevelOfExpression(callers, d.body)))

      case _ =>
        TlaLevelConst
    }
  }

  // Decls are always toplevel, so there are never callers
  def getLevelOfDecl(decl: TlaDecl): TlaLevel = {
    levelCacheMap.get(decl.name) match {
      case Some(level) => level

      case None =>
        decl match {
          case TlaConstDecl(_) =>
            TlaLevelConst

          case TlaVarDecl(_) =>
            TlaLevelState

          case TlaAssumeDecl(_) =>
            TlaLevelConst

          case TlaOperDecl(name, _, body) =>
            getLevelOfExpression(Set(name), body)

          case TlaTheoremDecl(_, _) =>
            TlaLevelConst
        }
    }
  }
}

object TlaLevelFinder {
  private val levelOfOper = Map(
      TlaActionOper.prime -> TlaLevelAction,
      TlaActionOper.enabled -> TlaLevelAction,
      TlaActionOper.unchanged -> TlaLevelAction,
      TlaActionOper.stutter -> TlaLevelAction,
      TlaActionOper.nostutter -> TlaLevelAction,
      TlaActionOper.composition -> TlaLevelAction,
      TlaTempOper.box -> TlaLevelTemporal,
      TlaTempOper.diamond -> TlaLevelTemporal,
      TlaTempOper.leadsTo -> TlaLevelTemporal,
      TlaTempOper.weakFairness -> TlaLevelTemporal,
      TlaTempOper.strongFairness -> TlaLevelTemporal,
      TlaTempOper.guarantees -> TlaLevelTemporal,
      TlaTempOper.AA -> TlaLevelTemporal,
      TlaTempOper.EE -> TlaLevelTemporal,
  )
}

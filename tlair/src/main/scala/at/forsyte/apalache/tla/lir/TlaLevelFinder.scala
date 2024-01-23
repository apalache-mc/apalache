package at.forsyte.apalache.tla.lir

import _root_.at.forsyte.apalache.tla.lir.oper.TlaActionOper
import _root_.at.forsyte.apalache.tla.lir.oper.TlaTempOper

class TlaLevelFinder(module: TlaModule) {
  private val consts = Set(module.constDeclarations.map(_.name): _*)
  private val vars = Set(module.varDeclarations.map(_.name): _*)
  private val defs = Map(module.operDeclarations.map { d => d.name -> d }: _*)
  private var levelCacheMap: Map[String, TlaLevel] = Map()
  var levelCacheGetFun: String => Option[TlaLevel] = (name: String) => levelCacheMap.get(name)
  var levelCacheSetFun = (name: String, level: TlaLevel) => levelCacheMap += name -> level

  def getLevelOfName(callers: Set[String], name: String): TlaLevel = {
    levelCacheGetFun(name) match {
      case Some(level) => level

      case None =>
        val computedLevel = if (consts.contains(name)) {
          TlaLevelConst
        } else if (vars.contains(name)) {
          TlaLevelState
        } else {
          if (!callers.contains(name) && defs.contains(name)) {
            val level = getLevelOfExpression(callers + name, defs(name).body)
            level
          } else {
            TlaLevelConst
          }
        }
        levelCacheSetFun(name, computedLevel)
        computedLevel
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

  /**
   * Generally, use when getting the level of a TlaDecl. If for any reason the cache should not be consulted, use
   * [[getLevelOfDeclWithoutCacheCheck]]
   */
  def getLevelOfDecl(decl: TlaDecl): TlaLevel = {
    levelCacheGetFun(decl.name) match {
      case Some(level) => level

      case None =>
        getLevelOfDeclWithoutCacheCheck(decl)
    }
  }

  /**
   * Used when getting the level of a TlaDecl and the cache should not be consulted.
   */
  def getLevelOfDeclWithoutCacheCheck(decl: TlaDecl): TlaLevel = {
    decl match {
      case TlaConstDecl(_) =>
        TlaLevelConst

      case TlaVarDecl(_) =>
        TlaLevelState

      case TlaAssumeDecl(_, _) =>
        TlaLevelConst

      case TlaOperDecl(name, _, body) =>
        val level = getLevelOfExpression(Set(name), body)
        levelCacheSetFun(name, level)
        level

      case TlaTheoremDecl(_, _) =>
        TlaLevelConst
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

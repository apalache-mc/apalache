package at.forsyte.apalache.tla.lir

/**
 * This class computes the level of a TLA+ declaration by using TlaExLevelFinder. See Lamport. Specifying Systems, p. 322.
 *
 * @param module a TLA module that contains the declarations to query
 * @author Igor Konnov
 */
class TlaDeclLevelFinder(module: TlaModule) {
  private val consts = Set(module.constDeclarations.map(_.name): _*)
  private val vars = Set(module.varDeclarations.map(_.name): _*)
  private val defs = Map(module.operDeclarations map { d => d.name -> d }: _*)
  private var levelCacheMap: Map[String, TlaLevel] = Map()

  def apply(decl: TlaDecl): TlaLevel = {
    decl match {
      case TlaConstDecl(_) =>
        TlaLevelConst

      case TlaVarDecl(_) =>
        TlaLevelState

      case TlaAssumeDecl(_) =>
        TlaLevelConst

      case TlaOperDecl(name, _, _) =>
        cacheLevel(Set(name), name)
        levelCacheMap(name)

      case TlaTheoremDecl(_, _) =>
        TlaLevelConst
    }
  }

  private def cacheLevel(callers: Set[String], name: String): Unit = {
    def levelOfName(name: String): TlaLevel = {
      if (consts.contains(name)) {
        TlaLevelConst
      } else if (vars.contains(name)) {
        TlaLevelState
      } else {
        if (!callers.contains(name) && defs.contains(name)) {
          // as the module comes from the parser, we assume that defs contains a definition for the name `name`
          cacheLevel(callers + name, name)
          levelCacheMap(name)
        } else {
          TlaLevelConst
        }
      }
    }

    val level = new TlaExLevelFinder(levelOfName)(defs(name).body)
    levelCacheMap += name -> level
  }
}

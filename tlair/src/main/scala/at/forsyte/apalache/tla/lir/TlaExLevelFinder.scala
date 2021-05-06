package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaTempOper}

/**
 * This class computes the level of a TLA+ expression. See Lamport. Specifying Systems, p. 322.
 *
 * @param nameLevel a function that returns the level of a name.
 * @author Igor Konnov
 */
class TlaExLevelFinder(nameLevel: String => TlaLevel) {
  def apply(ex: TlaEx): TlaLevel = find(ex)

  private def find: TlaEx => TlaLevel = {
    case NameEx(name) =>
      nameLevel(name)

    case OperEx(op, args @ _*) =>
      val level = TlaExLevelFinder.levelOfOper.getOrElse(op, TlaLevelConst)
      level.join(args.map(find))

    case LetInEx(body, defs @ _*) =>
      find(body).join(defs.map(d => find(d.body)))

    case _ =>
      TlaLevelConst
  }
}

object TlaExLevelFinder {
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
      TlaTempOper.EE -> TlaLevelTemporal
  )
}

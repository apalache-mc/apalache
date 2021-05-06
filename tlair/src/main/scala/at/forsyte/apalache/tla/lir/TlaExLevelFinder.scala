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

    case OperEx(op, args @ _*)
        if op == TlaActionOper.prime || op == TlaActionOper.enabled
          || op == TlaActionOper.unchanged || op == TlaActionOper.stutter
          || op == TlaActionOper.nostutter || op == TlaActionOper.composition =>
      TlaLevelAction.join(args.map(find))

    case OperEx(op, args @ _*)
        if op == TlaTempOper.box || op == TlaTempOper.diamond || op == TlaTempOper.leadsTo
          || op == TlaTempOper.weakFairness || op == TlaTempOper.strongFairness
          || op == TlaTempOper.guarantees || op == TlaTempOper.AA || op == TlaTempOper.EE =>
      TlaLevelTemporal.join(args.map(find))

    case OperEx(_, args @ _*) =>
      TlaLevelConst.join(args.map(find))

    case LetInEx(body, defs @ _*) =>
      find(body).join(defs.map(d => find(d.body)))

    case _ =>
      TlaLevelConst
  }
}

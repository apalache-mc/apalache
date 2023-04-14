//package at.forsyte.apalache.tla.pp.arenas
//import at.forsyte.apalache.tla.bmcmt.PureArena
//import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
//
///**
// * @author
// *   Jure Kukovec
// */
//class ArenaNeutralRules extends ArenaRule {
//  override def isDefinedAt(x: TlaEx): Boolean = true
//
//  override def apply(v1: TlaEx): PureArena = {
//    case _: ValEx => PureArena.empty
//    case _:
//  }
//}

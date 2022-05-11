package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.values.TlaBool

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TemporalEncoder(module: TlaModule, gen: UniqueNameGenerator) extends LazyLogging {
  import TemporalEncoder.NAME_PREFIX
  val levelFinder = new TlaLevelFinder(module)

  def encodeInvariants(invariants: List[String], init: String, next: String): TlaModule = {
    val temporalInvariants = invariants.filter(invName => {
      module.declarations.find(_.name == invName) match {
        case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
          // either a state invariant, or an action invariant
          val level = levelFinder.getLevelOfDecl(inv)
          level == TlaLevelTemporal
        case _ => false
      }
    })

    if(temporalInvariants.isEmpty){
      logger.info("  > No temporal properties found, nothing to encode")
      module
    } else {
      logger.info(s"  > Found ${temporalInvariants.length} temporal invariants")
      logger.info(s"  > Adding logic for loop finding")

      val initDecl = module.declarations.find(_.name == init)
      if(initDecl.isEmpty){
        logger.info(s"  > init predicate named `${init}` not found, cannot encode")
        module
      }

      val nextDecl = module.declarations.find(_.name == next)
      if(nextDecl.isEmpty){
        logger.info(s"  > next predicate named `${next}` not found, cannot encode")
        module
      }
      val moduleWithLoopLogic = addLoopLogic(module, initDecl.get, nextDecl.get)
      moduleWithLoopLogic
    }
  }

  // def encode(invName: String, optViewName: Option[String] = None): TlaModule = {
  //   module.declarations.find(_.name == invName) match {
  //     case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
  //       // either a state invariant, or an action invariant
  //       val level = levelFinder.getLevelOfDecl(inv)
  //       level match {
  //         case TlaLevelTemporal =>
  //           logger.info("  > Encoding temporal property")
  //           logger.info(inv.formalParams.toString())
  //           encodeExpression(module, inv.body)
  //         case _ =>
  //           logger.info("  > Not a temporal property, nothing to encode")
  //           module
  //       }

  //     case _ =>
  //       throw new TlaInputError(s"  > Invariant is not in proper form, nothing to encode", None)
  //   }
  // }

  def createLoopVariables(originalVariables: Set[TlaVarDecl]): Set[TlaVarDecl] = {
    originalVariables.map(varDecl =>
      createLoopVariableForVariable(varDecl))
  }

  def createLoopVariableForVariable(varDecl: TlaVarDecl): TlaVarDecl = {
      TlaVarDecl(s"${NAME_PREFIX}Loop_${varDecl.name}_${gen.newName()}")(varDecl.typeTag)
  }

  def addLoopLogic(module: TlaModule, init: TlaDecl, next: TlaDecl): TlaModule = {
    val onLoop = TlaVarDecl(s"${NAME_PREFIX}InLoop_${gen.newName()}")(Typed(BoolT1))
    val loopVariables = createLoopVariables(Set.from(module.varDeclarations)) + onLoop

    print("init: \n" + init + "\n")

    print("next: \n" + next + "\n")
    

    new TlaModule(module.name, module.declarations ++ loopVariables)
  }
}

object TemporalEncoder {
  val NAME_PREFIX = ""
}

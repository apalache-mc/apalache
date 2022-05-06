package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.io.UsableAsTLAIdentifierPrinter

/**
 * <p>Encode temporal operators.</p>
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TemporalEncoder(gen: UniqueNameGenerator) extends LazyLogging {

  def encode(module: TlaModule, invName: String, optViewName: Option[String] = None): TlaModule = {
    val levelFinder = new TlaDeclLevelFinder(module)

    module.declarations.find(_.name == invName) match {
      case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
        // either a state invariant, or an action invariant
        val level = levelFinder(inv)
        level match {
          case TlaLevelTemporal =>
            logger.info("  > Encoding temporal property")
            logger.info(inv.formalParams.toString())
            encodeExpression(module, inv.body)
          case _ =>
            logger.info("  > Not a temporal property, nothing to encode")
            module
        }

      case _ =>
        throw new TlaInputError(s"  > Invariant is not in proper form, nothing to encode", None)
    }
  }

  def encodeExpression(module: TlaModule, expr: TlaEx): TlaModule = {
    val levelFinder = new TlaDeclLevelFinder(module)

    // logger.info(expr)
    module

  }
}

object TemporalEncoder {
  def apply(gen: UniqueNameGenerator): TemporalEncoder = {
    new TemporalEncoder(gen)
  }
}

package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}

import javax.inject.Singleton

/**
 * <p>Encode temporal operators.</p>
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TemporalEncoder(gen: UniqueNameGenerator) {

  def encode(mod: TlaModule, invName: String, optViewName: Option[String] = None): TlaModule = {
    mod
  }
}

object TemporalEncoder {
  def apply(gen: UniqueNameGenerator): TemporalEncoder = {
    new TemporalEncoder(gen)
  }
}

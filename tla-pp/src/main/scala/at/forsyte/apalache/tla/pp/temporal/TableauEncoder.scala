package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.values.TlaPredefSet
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.typecomp._
import scalaz._
import scalaz.Scalaz._

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TableauEncoder(module: TlaModule, gen: UniqueNameGenerator) extends LazyLogging {
  def encodeInvariant(module: TlaModule, init: TlaOperDecl, next: TlaOperDecl, loopOk: TlaOperDecl, invariant: TlaOperDecl): (TlaModule, TlaOperDecl, TlaOperDecl, TlaOperDecl) = {

    invariant match {
      case _ => 
    }

    (module, init, next, loopOk)
  }
}

object TableauEncoder {
  val NAME_PREFIX = ""
}

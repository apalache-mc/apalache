package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, TypeComputationFactory}

/**
 * Base builder class that offers `buildBySignatureLookup` to other builders.
 *
 * `buildBySignatureLookup` creates a `composeAndValidateTypes` call, for an operator with a known signature.
 *
 * @author
 *   Jure Kukovec
 */
trait ProtoBuilder {
  protected val cmpFactory: TypeComputationFactory = new TypeComputationFactory

  /**
   * Specialized `composeAndValidateTypes`, applicable when the TNT operator has a signature, that is, it is not
   * overloaded. In that case, we fetch the computation from the [[TypeComputationFactory]].
   */
  protected def buildBySignatureLookup(oper: TlaOper, args: TlaEx*): TlaEx =
    BuilderUtil.composeAndValidateTypes(oper, cmpFactory.computationFromSignature(oper), args: _*)
}

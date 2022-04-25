package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecmp.{BuilderUtil, SignatureHandler}

/**
 * Base builder class that offers `simpleInstruction` to other builders.
 *
 * `simpleInstruction` creates a `buildInstruction` call, for an operator with a known signature.
 *
 * @author
 *   Jure Kukovec
 */
trait ProtoBuilder {
  protected val varPool: TypeVarPool
  protected val sigGen: SignatureHandler = new SignatureHandler(varPool)

  /**
   * Specialized `buildInstruction`, applicable when the TNT operator has a signature, that is, it is not overloaded. In
   * that case, we fetch the computation from the [[SignatureHandler]].
   */
  protected def simpleInstruction(oper: TlaOper, args: TlaEx*): TlaEx =
    BuilderUtil.buildInstruction(oper, sigGen.computationFromSignature(oper), args: _*)
}

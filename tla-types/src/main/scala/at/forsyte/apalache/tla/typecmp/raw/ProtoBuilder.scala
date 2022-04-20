package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecmp.{BuildInstruction, SignatureGenerator}

/**
 * Base builder class that offers `simpleInstruction` to other builders.
 *
 * `simpleInstruction` creates a `BuildInstruction`, for an operator with a known signature.
 *
 * @author
 *   Jure Kukovec
 */
trait ProtoBuilder {
  protected val varPool: TypeVarPool
  protected val sigGen: SignatureGenerator = new SignatureGenerator(varPool)

  // Build instruction for the case where the TNT operator has a signature, that is,
  // it is not overloaded. In that case, we just resolve signatures
  protected def simpleInstruction(oper: TlaOper, nArgs: Int): BuildInstruction =
    BuildInstruction(oper, sigGen.computationFromSignature(oper, nArgs))
}

package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecmp.{BuildInstruction, SignatureGenerator}

/**
 * @author
 *   Jure Kukovec
 */
trait ProtoBuilder {
  protected val sigGen: SignatureGenerator

  // Build instruction for the case where the TNT operator has a signature, that is,
  // it is not overloaded. In that case, we just resolve signatures
  protected def simpleInstruction(oper: TlaOper, nArgs: Int): BuildInstruction =
    BuildInstruction(oper, sigGen.computationFromSignature(oper, nArgs))
}

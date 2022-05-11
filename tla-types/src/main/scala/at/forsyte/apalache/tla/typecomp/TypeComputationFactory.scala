package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier, TypeVarPool}
import at.forsyte.apalache.tla.typecomp.BuilderUtil.throwMsg
import at.forsyte.apalache.tla.typecomp.signatures._

/**
 * Some TNT operators have signatures (see [[signatures]]). TypeComputationFactory collects [[SignatureMap]]s for such
 * operators and constructs signature-matching [[PureTypeComputation]]s on demand.
 *
 * @author
 *   Jure Kukovec
 */
class TypeComputationFactory {

  private val baseOperMap: SignatureMap = BaseOperSignatures.getMap
  private val aritOperMap: SignatureMap = ArithOperSignatures.getMap
  private val boolOperMap: SignatureMap = BoolOperSignatures.getMap
  private val setOperMap: SignatureMap = SetOperSignatures.getMap
  private val seqOperMap: SignatureMap = SeqOperSignatures.getMap

  private val knownSignatures: SignatureMap = baseOperMap ++ aritOperMap ++ boolOperMap ++ setOperMap ++ seqOperMap

  /** Given an operator with a known signature, constructs a pure type computation for its return type */
  def computationFromSignature(oper: TlaOper): PureTypeComputation = { args =>
    val arity = args.size
    knownSignatures.get(oper) match {
      // Failure: bad identifier or arity
      case None      => throwMsg(s"Unknown signature for operator ${oper.name} and arity $arity.")
      case Some(sig) => sig(args)
    }
  }
}

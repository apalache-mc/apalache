package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.BuilderUtil.leftTypeException
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
  private val arithOperMap: SignatureMap = ArithOperSignatures.getMap
  private val boolOperMap: SignatureMap = BoolOperSignatures.getMap
  private val setOperMap: SignatureMap = SetOperSignatures.getMap
  private val finSetOperMap: SignatureMap = FiniteSetOperSignatures.getMap
  private val seqOperMap: SignatureMap = SeqOperSignatures.getMap
  private val actionOperMap: SignatureMap = ActionOperSignatures.getMap
  private val controlOperMap: SignatureMap = ControlOperSignatures.getMap
  private val funOperMap: SignatureMap = FunOperSignatures.getMap
  private val tempOperMap: SignatureMap = TemporalOperSignatures.getMap
  private val apaInternalOperMap: SignatureMap = ApalacheInternalOperSignatures.getMap
  private val apaOperMap: SignatureMap = ApalacheOperSignatures.getMap
  private val varOperMap: SignatureMap = VariantOperSignatures.getMap

  private val knownSignatures: SignatureMap =
    baseOperMap ++ arithOperMap ++ boolOperMap ++ setOperMap ++ seqOperMap ++
      actionOperMap ++ controlOperMap ++ funOperMap ++ finSetOperMap ++ tempOperMap ++
      apaInternalOperMap ++ apaOperMap ++ varOperMap

  /** Given an operator with a known signature, constructs a pure type computation for its return type */
  def computationFromSignature(oper: TlaOper): PureTypeComputation = { args =>
    knownSignatures.get(oper) match {
      // Failure: bad identifier
      case None      => leftTypeException(s"Unknown signature for operator ${oper.name}.")
      case Some(sig) => sig(args)
    }
  }
}

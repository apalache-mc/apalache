package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier, TypeVarPool}
import at.forsyte.apalache.tla.typecomp.BuilderUtil.throwMsg
import at.forsyte.apalache.tla.typecomp.signatures.{ArithOperSignatures, BoolOperSignatures, SetOperSignatures}

/**
 * Some TNT operators have signatures (see [[signatures]]). TypeComputationFactory collects [[SignatureGenerator]]s for
 * such operators and constructs signature-matching [[PureTypeComputation]]s on demand.
 *
 * @author
 *   Jure Kukovec
 */
class TypeComputationFactory(varPool: TypeVarPool) {

  private val aritOperMap: SignatureGenMap = ArithOperSignatures.getMap
  private val boolOperMap: SignatureGenMap = BoolOperSignatures.getMap(varPool)
  private val setOperMap: SignatureGenMap = SetOperSignatures.getMap(varPool)

  private val unifier: TypeUnifier = new TypeUnifier(varPool)

  private val knownSignatures: SignatureGenMap = aritOperMap ++ boolOperMap ++ setOperMap

  /** Given an operator and arity (important for polyadic operators), returns a signature, if known */
  def getSignature(oper: TlaOper, arity: Int): Option[OperT1] =
    if (!oper.arity.cond(arity)) None
    else knownSignatures.get(oper).map(_(arity))

  /** Given an operator with a known signature, constructs a pure type computation for its return type */
  def computationFromSignature(oper: TlaOper): PureTypeComputation = { args =>
    val arity = args.size
    getSignature(oper, arity) match {
      // Failure case 1: bad identifier or arity
      case None                   => throwMsg(s"Unknown signature for operator ${oper.name} and arity $arity.")
      case Some(OperT1(from, to)) =>
        // Failure case 2: arity mismatch. This should only happen if one of the signatures is implemented incorrectly
        val arityInMap = from.size
        if (arityInMap != arity)
          throwMsg(s"Incompatible arity for operator ${oper.name}: Expected $arityInMap arguments, got $arity")
        else {
          // If we have an operator signature, we need to construct a substitution (see ScopedBuilder guarantees)
          // This substitution tells us what monotype is obtained by applying a polymorphic operator
          // to arguments with monotypes
          val totalSubOpt = from.zip(args).foldLeft(Option(Substitution.empty)) { case (subOpt, (argT, paramT)) =>
            subOpt.flatMap(s => unifier.unify(s, argT, paramT).map(_._1))
          }
          totalSubOpt
            .map(sub => liftRet(sub.subRec(to))) // we apply it to the (polymorphic) return type given by the signature
            .getOrElse(
                // Failure case 3: Can't unify
                throwMsg(
                    s"${oper.name} expects arguments of types (${from.mkString(", ")}), found: (${args.mkString(", ")})"
                )
            )
        }
    }
  }
}

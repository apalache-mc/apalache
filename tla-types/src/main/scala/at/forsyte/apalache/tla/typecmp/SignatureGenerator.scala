package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{FixedArity, TlaOper}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier, TypeVarPool}
import at.forsyte.apalache.tla.typecmp.BuilderUtil.throwMsg
import at.forsyte.apalache.tla.typecmp.signatures.{ArithOperSignatures, BoolOperSignatures, SetOperSignatures}

/**
 * Some TNT operators have signatures. SignatureGenerator serves them, from the operator identifier.
 *
 * @author
 *   Jure Kukovec
 */
class SignatureGenerator(varPool: TypeVarPool) {

  private val aritOperMap: SignatureMap = ArithOperSignatures.getMap
  private val boolOperMap: SignatureMap = BoolOperSignatures.getMap(varPool)
  private val setOperMap: SignatureMap = SetOperSignatures.getMap(varPool)

  private val knownSignatures: SignatureMap = aritOperMap ++ boolOperMap ++ setOperMap

  // Given an operator and arity (important for polyadic opers), returns a signature, if known
  def getSignature(oper: TlaOper, arity: Int): Option[OperT1] =
    if (!oper.arity.cond(arity)) None
    else knownSignatures.get(oper).map(_(arity))

  // Convenience method, when we know the operator has fixed arity
  def getSignatureForFixedArity(oper: TlaOper): Option[OperT1] = oper.arity match {
    case FixedArity(n) => getSignature(oper, n)
    case _             => None
  }

  // Given an operator with a known signature, constructs a pure type computation for its return type
  def computationFromSignature(oper: TlaOper): pureTypeComputation = { args =>
    val arity = args.size
    getSignature(oper, arity) match {
      // Failure case 1: bad identifier or arity
      case None => throwMsg(s"${oper.name} is not an operator with a known signature for arity $arity.")
      case Some(OperT1(from, to)) =>
        // Failure case 2: arity mismatch. This should only happen if one of the signatures is implemented incorrectly
        if (from.length != args.length)
          throwMsg(
              s"Incompatible arity for operator ${oper.name}: Expected ${from.length} arguments, got ${args.length}")
        else {
          // If we have an operator signature, we need to construct a substitution (see ScopedBuilder guarantees)
          // this substitution tells us what monotype is obtained by applying a polymorphic operator
          // to arguments wiht monotypes
          val totalSubOpt = from.zip(args).foldLeft(Option(Substitution.empty)) { case (subOpt, (argT, paramT)) =>
            subOpt.flatMap(s => singleUnification(argT, paramT, s).map(_._1))
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

  // Performs unificaiton on 2 types with a fresh unifier
  private def singleUnification(
      lhs: TlaType1,
      rhs: TlaType1,
      subst: Substitution): Option[(Substitution, TlaType1)] = {
    (new TypeUnifier).unify(subst, lhs, rhs)
  }

}

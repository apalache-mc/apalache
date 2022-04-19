package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{FixedArity, TlaArithOper, TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeVarPool}
import at.forsyte.apalache.tla.typecmp.BuilderUtil.throwMsg

import scala.language.implicitConversions

/**
 * Some TNT operators have signatures. SignatureResolver serves them, from the operator identifier.
 *
 * @author
 *   Jure Kukovec
 */
class SignatureGenerator(varPool: TypeVarPool) {

  // Implicit lifting, for monotyped, fixed-arity operators
  implicit def liftOper(operT1: OperT1): Int => OperT1 = _ => operT1

  type SignatureMap = Map[TlaOper, Int => OperT1]

  private val arithOperMap: SignatureMap = {
    import TlaArithOper._

    val intOpers = Seq(
        plus,
        minus,
        mult,
        div,
        mod,
        exp,
    ).map { _ -> liftOper(OperT1(Seq(IntT1(), IntT1()), IntT1())) }.toMap

    val boolOpers: SignatureMap = Seq(
        lt,
        gt,
        le,
        ge,
    ).map { _ -> liftOper(OperT1(Seq(IntT1(), IntT1()), BoolT1())) }.toMap

    val rest: SignatureMap = Map(
        TlaArithOper.uminus -> OperT1(Seq(IntT1()), IntT1()),
        TlaArithOper.dotdot -> OperT1(Seq(IntT1(), IntT1()), SetT1(IntT1())),
    )
    intOpers ++ boolOpers ++ rest
  }

  private val boolOperMap: SignatureMap = {
    import TlaBoolOper._

    val polyadic: SignatureMap = Seq(
        and,
        or,
    ).map {
      _ -> { n: Int =>
        OperT1(Seq.fill(n)(BoolT1()), BoolT1())
      }
    }.toMap

    val binary: SignatureMap = Seq(
        implies,
        equiv,
    ).map { _ -> liftOper(OperT1(Seq(BoolT1(), BoolT1()), BoolT1())) }.toMap

    val boundedQuant: SignatureMap = Seq(
        forall,
        exists,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        val setT = SetT1(t)
        OperT1(Seq(t, setT, BoolT1()), BoolT1())
      }
    }.toMap

    val unboundedQuant: SignatureMap = Seq(
        forallUnbounded,
        existsUnbounded,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        OperT1(Seq(t, BoolT1()), BoolT1())
      }
    }.toMap

    val rest: SignatureMap =
      Map(
          not -> OperT1(Seq(BoolT1()), BoolT1())
      )

    polyadic ++ binary ++ boundedQuant ++ unboundedQuant ++ rest
  }

  private val knownSignatures: SignatureMap =
    arithOperMap ++ boolOperMap ++
      Map(
          TlaSetOper.cup -> { _: Int =>
            val t = varPool.fresh
            val setT = SetT1(t)
            OperT1(Seq(setT, setT), setT)
          }
      )

  def getSignatureForFixedArity(oper: TlaOper): Option[OperT1] = {
    oper.arity match {
      case FixedArity(n) => getSignature(oper, n)
      case _             => None
    }
  }

  def getSignature(oper: TlaOper, arity: Int): Option[OperT1] = {
    assert(oper.arity.cond(arity)) // Oper accepts this arity
    knownSignatures.get(oper).map(_(arity))
  }

  def computationFromSignatureForFixedArity(oper: TlaOper): pureTypeComputation = oper.arity match {
    case FixedArity(n) => computationFromSignature(oper, n)
    case _             => throw new BuilderError(s"${oper.name} does not have fixed arity.")
  }

  def computationFromSignature(oper: TlaOper, arity: Int): pureTypeComputation = { args =>
    getSignature(oper, arity) match {
      // Failure case 1: bad identifier
      case None                   => throwMsg(s"${oper.name} is not an operator with a known signature.")
      case Some(OperT1(from, to)) =>
        // Failure case 2: arity mismatch
        if (from.length != args.length)
          throwMsg(
              s"Incompatible arity for operator ${oper.name}: Expected ${from.length} arguments, got ${args.length}")
        else {
          val totalSubOpt = from.zip(args).foldLeft(Option(Substitution.empty)) { case (subOpt, (argT, paramT)) =>
            subOpt.flatMap(s => singleUnification(argT, paramT, s).map(_._1))
          }
          totalSubOpt
            .map(sub => liftRet(sub.subRec(to)))
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

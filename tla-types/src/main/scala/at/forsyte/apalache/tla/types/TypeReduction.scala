package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.BoolFormula

sealed case class ReductionResult(t: SmtDatatype, phi: Seq[BoolFormula])

class TypeReduction(private val gen: SmtVarGenerator) {
  def apply(tau: TlaType, m: typeContext): ReductionResult = tau match {
    case t: TypeVar => ReductionResult(m(t), Seq.empty)
    case IntT       => ReductionResult(int, Seq.empty)
    case StrT       => ReductionResult(str, Seq.empty)
    case BoolT      => ReductionResult(bool, Seq.empty)
    case SetT(tauPrime) =>
      val ReductionResult(v, phi) = apply(tauPrime, m)
      ReductionResult(set(v), phi)
    case SeqT(tauPrime) =>
      val ReductionResult(v, phi) = apply(tauPrime, m)
      ReductionResult(seq(v), phi)
    case FunT(domT, cdmT) =>
      val ReductionResult(v1, phi1) = apply(domT, m)
      val ReductionResult(v2, phi2) = apply(cdmT, m)
      ReductionResult(fun(v1, v2), phi1 ++ phi2)
    case OperT(domT, cdmT) =>
      val ReductionResult(v1, phi1) = apply(domT, m)
      val ReductionResult(v2, phi2) = apply(cdmT, m)
      ReductionResult(oper(v1, v2), phi1 ++ phi2)
    case TupT(ts @ _*) =>
      val l = ts.length
      val results = ts map { apply(_, m) }
      val tupIdx = gen.getFreshInt
      val constraints = results.zipWithIndex.flatMap { case (ReductionResult(ti, phii), i) =>
        hasIndex(tupIdx, i, ti) +: phii
      }
      val phi = sizeOfEql(tupIdx, l) +: constraints
      ReductionResult(tup(tupIdx), phi)
    case RecT(ts @ _*) =>
      val l = ts.length
      val recIdx = gen.getFreshInt
      val constraints = ts flatMap { case KvPair(k, v) =>
        val ReductionResult(t, phi) = apply(v, m)
        hasField(recIdx, k, t) +: phi
      }
      ReductionResult(rec(recIdx), constraints)
    case SparseTupT(ts @ _*) =>
      val l = ts.length
      val tupIdx = gen.getFreshInt
      val constraints = ts flatMap { case KvPair(k, v) =>
        val ReductionResult(t, phi) = apply(v, m)
        hasIndex(tupIdx, k, t) +: phi
      }
      ReductionResult(tup(tupIdx), constraints)
  }
}
